use std::{
    collections::{HashMap, HashSet},
    fmt,
    hash::Hash,
    sync::Arc,
};

use crate::{
    language::Language,
    lower::{Alternative, NonTerminal, Term, Terminal},
    util::DisplayWithDb,
    Db, Span,
};

use super::{lr0_parse_table, Lr0ParseTable, Lr0StateId};

#[derive(Debug, Clone)]
pub struct TermString {
    parse_table: Arc<Lr0ParseTable>,
    locations: Vec<Location>,
}

impl PartialEq<TermString> for TermString {
    fn eq(&self, other: &TermString) -> bool {
        Arc::ptr_eq(&self.parse_table, &other.parse_table) && self.locations == other.locations
    }
}
impl Eq for TermString {}
impl PartialOrd for TermString {
    fn partial_cmp(&self, other: &TermString) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TermString {
    fn cmp(&self, other: &TermString) -> std::cmp::Ordering {
        Ord::cmp(
            &(Arc::as_ptr(&self.parse_table) as usize),
            &(Arc::as_ptr(&other.parse_table) as usize),
        )
        .then_with(|| self.locations.cmp(&other.locations))
    }
}
impl Hash for TermString {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (Arc::as_ptr(&self.parse_table) as usize).hash(state);
        self.locations.hash(state);
    }
}

impl TermString {
    pub fn new(db: &dyn Db, language: Language, terms: Vec<Term>) -> Self {
        let parse_table = lr0_parse_table(
            db,
            language,
            NonTerminal::new_internal(
                db,
                Alternative::new(db, Span { start: 0, end: 0 }, terms, None),
            ),
        );
        TermString {
            parse_table,
            locations: vec![Location {
                tree: Tree {
                    terminals: 0,
                    children: None,
                },
                state: Lr0StateId(0),
            }],
        }
    }

    pub fn next<'a>(&'a self, db: &'a dyn Db) -> (bool, HashMap<Terminal, HashSet<TermString>>) {
        let mut contains_empty = false;
        let mut derivative: HashMap<Terminal, HashSet<TermString>> = HashMap::new();

        let mut stack = vec![(
            self.locations.clone(),
            (self.locations.len(), HashSet::new()),
        )];
        while let Some((locations, (min_len, visited))) = stack.pop() {
            let current_loc = locations.last().unwrap();
            let state = &self.parse_table[current_loc.state];
            for (terminal, state) in &state.actions {
                let mut locations = locations.clone();
                locations.push(Location {
                    tree: Tree {
                        terminals: 1,
                        children: None,
                    },
                    state: *state,
                });
                derivative
                    .entry(terminal.clone())
                    .or_default()
                    .insert(TermString {
                        parse_table: self.parse_table.clone(),
                        locations,
                    });
            }
            for (item, _) in &state.item_set {
                let num_terms = item.alternative.terms(db).len();
                if item.index < num_terms {
                    // Shift not a reduction
                    continue;
                }
                if item.non_terminal.is_internal(db) {
                    // The internal non-terminal is the top level so we're done
                    contains_empty = true;
                    continue;
                }
                let (new_locations, reduced) = locations.split_at(locations.len() - num_terms);
                let mut locations = new_locations.to_vec();
                let new_loc =
                    self.parse_table[locations.last().unwrap().state].goto[&item.non_terminal];
                let (min_len, visited) = if min_len < locations.len() {
                    let mut visited = visited.clone();
                    if !visited.insert(new_loc) {
                        // Infinitely looping non-terminals
                        // TODO: Maybe this is the best place to emit a diagnostic?
                        continue;
                    }
                    (min_len, visited)
                } else {
                    (locations.len(), HashSet::new())
                };
                locations.push(Location {
                    tree: Tree {
                        terminals: reduced.iter().map(|loc| loc.tree.terminals).sum(),
                        children: Some(reduced.into()),
                    },
                    state: new_loc,
                });
                stack.push((locations, (min_len, visited)));
            }
        }
        (contains_empty, derivative)
    }

    /// Check for any loops that we're currently in that could generate exactly
    /// the same set of non-terminals again and call the callback with the
    /// number of terminals in that loop.
    pub(super) fn loop_lengths(&self, mut callback: impl FnMut(u32)) {
        // TODO: This would be way nicer as a generator.
        // TODO: It feels like there should be a more efficient way of doing this,
        // lots of caching is available too.
        let mut tail_len = 0;
        for (end, end_loc) in self.locations.iter().enumerate().rev() {
            let path = &self.locations[end..];
            let mut left_recursive = &end_loc.tree;
            while let Some([left_child, rest @ ..]) = left_recursive.children.as_deref() {
                left_recursive = &left_child.tree;

                path_prefixes_of_tree(&path[1..], rest, 0, &mut |prefix_len| {
                    callback(tail_len + end_loc.tree.terminals - prefix_len);
                });
            }
            let mut loop_len = end_loc.tree.terminals;
            for (start, start_loc) in self.locations[..end].iter().enumerate().rev() {
                if start_loc.state != end_loc.state {
                    continue;
                }
                // We've found a loop from start to end, now we check that the
                // path we've taken from end could be the start of that loop.
                path_prefixes_of_tree(
                    &path[1..],
                    &self.locations[start + 1..end],
                    0,
                    &mut |prefix_len| {
                        callback(tail_len + loop_len - prefix_len);
                    },
                );
                loop_len += start_loc.tree.terminals;
            }
            tail_len += end_loc.tree.terminals;
        }
    }
}

impl DisplayWithDb for TermString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        // TODO: Print out trees too?
        // TODO: How are you meant to know what the states are?
        write!(f, "{}: 0", self.parse_table.goal.display(db))?;
        for location in &self.locations[1..] {
            write!(f, " (#{}) {}", location.tree.terminals, location.state)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Location {
    tree: Tree,
    state: Lr0StateId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Tree {
    terminals: u32,
    children: Option<Arc<[Location]>>,
}

fn path_prefixes_of_tree(
    mut path: &[Location],
    mut tree: &[Location],
    mut prefix_len: u32,
    callback: &mut impl FnMut(u32),
) {
    while let [path_loc, remaining_path @ ..] = path {
        let [tree_loc, remaining_tree @ ..] = tree else {
            return;
        };
        if let Some(children) = &tree_loc.tree.children {
            path_prefixes_of_tree(path, children, prefix_len, callback);
        }
        if path_loc.state != tree_loc.state {
            return;
        }
        path = remaining_path;
        tree = remaining_tree;
        prefix_len += tree_loc.tree.terminals;
    }
    callback(prefix_len);
}
