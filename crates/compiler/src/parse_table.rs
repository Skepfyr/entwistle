use std::{
    collections::{hash_map::Entry, BTreeSet, HashMap, HashSet},
    fmt::{self, Write as _},
    hash::Hash,
    ops::Index,
    sync::Arc,
};

use im::OrdSet;
use indenter::indented;
use tracing::{debug, instrument, trace};

use crate::{
    language::Ident,
    lower::{self, Lower, NonTerminal, NonTerminalData, Term, Terminal},
    util::DbDisplay,
};

#[salsa::query_group(ParseTableStorage)]
pub trait ParseTable: Lower {
    #[salsa::interned]
    fn intern_item_set(&self, data: ItemSetData) -> ItemSet;
    fn first_set(&self, non_terminal: NonTerminal) -> (bool, OrdSet<Terminal>);
    fn lr0_parse_table(&self) -> Lr0ParseTable;
    fn parse_table(&self) -> LrkParseTable;
    fn normal_production(&self, non_terminal: NormalNonTerminal) -> OrdSet<Arc<[NormalTerm]>>;
    fn left_recursive(&self, non_terminal: NonTerminal) -> bool;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LrkParseTable {
    start_states: HashMap<Ident, StateId>,
    states: Arc<[State]>,
}

impl<Db: ParseTable + ?Sized> DbDisplay<Db> for LrkParseTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result {
        writeln!(f, "Start states:")?;
        for (ident, state) in &self.start_states {
            writeln!(f, "  {} => {}", ident.display(db), state)?;
        }
        for (i, state) in self.states.iter().enumerate() {
            writeln!(f, "State {}:", i)?;
            writeln!(f, "  Actions:")?;
            write!(indented(f).with_str("    "), "{}", state.action.display(db))?;
            writeln!(f, "  Goto:")?;
            for (&nt, &state) in &state.goto {
                writeln!(f, "    {} -> {}", nt.display(db), state)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StateId(usize);

impl fmt::Display for StateId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    action: Action,
    goto: HashMap<NonTerminal, StateId>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Action {
    Ambiguous(Arc<[(Terminal, Action)]>),
    Shift(Terminal, StateId),
    Reduce(NonTerminal, Arc<[Term]>),
}

impl<Db: ParseTable + ?Sized> DbDisplay<Db> for Action {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result {
        fn display<Db: ParseTable + ?Sized>(
            db: &Db,
            action: &Action,
            f: &mut fmt::Formatter<'_>,
            lookahead: &mut Vec<Terminal>,
        ) -> fmt::Result {
            match action {
                Action::Ambiguous(ambiguities) => {
                    for (terminal, action) in &**ambiguities {
                        lookahead.push(*terminal);
                        display(db, action, f, lookahead)?;
                        lookahead.pop();
                    }
                    Ok(())
                }
                Action::Shift(terminal, state) => {
                    for terminal in lookahead {
                        write!(f, "{} ", terminal.display(db))?;
                    }
                    writeln!(f, ": {} -> {}", terminal.display(db), state)
                }
                Action::Reduce(non_terminal, production) => {
                    for terminal in lookahead {
                        write!(f, "{} ", terminal.display(db))?;
                    }
                    write!(f, ": {} ->", non_terminal.display(db))?;
                    for term in &**production {
                        write!(f, " {}", term.display(db))?;
                    }
                    writeln!(f)
                }
            }
        }
        display(db, self, f, &mut Vec::new())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Item {
    pub non_terminal: NonTerminal,
    pub production: Arc<[Term]>,
    pub index: usize,
}

impl Item {
    fn new(non_terminal: NonTerminal, production: Arc<[Term]>) -> Self {
        Self {
            non_terminal,
            production,
            index: 0,
        }
    }

    fn next(&self) -> Option<Term> {
        self.production.get(self.index).copied()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lr0StateId(usize);

impl fmt::Display for Lr0StateId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ItemIndex {
    state: Lr0StateId,
    item: usize,
}

impl fmt::Display for ItemIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.state, self.item)
    }
}

pub fn first_set(db: &dyn ParseTable, non_terminal: NonTerminal) -> (bool, OrdSet<Terminal>) {
    db.production(non_terminal)
        .into_iter()
        .map(|terms| terms.get(0).copied())
        .fold(
            (false, OrdSet::new()),
            |(contains_null, mut set), term| match term {
                Some(Term::Terminal(terminal)) => {
                    set.insert(terminal);
                    (contains_null, set)
                }
                Some(Term::NonTerminal(nt)) if nt != non_terminal => {
                    let other = db.first_set(nt);
                    (contains_null | other.0, set.union(other.1))
                }
                Some(Term::NonTerminal(_)) => (contains_null, set),
                None => (true, set),
            },
        )
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lr0ParseTable {
    pub start_states: HashMap<Ident, Lr0StateId>,
    pub states: Vec<Lr0State>,
}

impl<Db: ParseTable + ?Sized> DbDisplay<Db> for Lr0ParseTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result {
        writeln!(f, "Start states:")?;
        for (ident, state) in &self.start_states {
            writeln!(f, "  {} => {}", ident.display(db), state)?;
        }
        for (i, state) in self.states.iter().enumerate() {
            writeln!(f, "State {}:", i)?;
            writeln!(f, "  Items:")?;
            for (item, _backlinks) in &state.item_set {
                write!(f, "    {} ->", item.non_terminal.display(db))?;
                for term in &item.production[..item.index] {
                    write!(f, " {}", term.display(db))?;
                }
                print!(" .");
                for term in &item.production[item.index..] {
                    write!(f, " {}", term.display(db))?;
                }
                writeln!(f)?;
            }
            writeln!(f, "  Actions:")?;
            for (&t, &state) in &state.actions {
                writeln!(f, "    {} -> {}", t.display(db), state)?;
            }
            for (&nt, &state) in &state.goto {
                writeln!(f, "    {} -> {}", nt.display(db), state)?;
            }
        }
        Ok(())
    }
}

impl Index<Lr0StateId> for Lr0ParseTable {
    type Output = Lr0State;

    fn index(&self, index: Lr0StateId) -> &Self::Output {
        &self.states[index.0]
    }
}

impl Index<ItemIndex> for Lr0ParseTable {
    type Output = (Item, BTreeSet<ItemIndex>);

    fn index(&self, index: ItemIndex) -> &Self::Output {
        &self[index.state].item_set[index.item]
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lr0State {
    pub item_set: Vec<(Item, BTreeSet<ItemIndex>)>,
    pub actions: HashMap<Terminal, Lr0StateId>,
    pub goto: HashMap<NonTerminal, Lr0StateId>,
}

intern_key!(ItemSet);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ItemSetData {
    items: Vec<(Item, BTreeSet<ItemIndex>)>,
}

pub fn lr0_parse_table(db: &dyn ParseTable) -> Lr0ParseTable {
    let mut states: Vec<Lr0State> = Vec::new();
    let mut state_lookup: HashMap<BTreeSet<Item>, Lr0StateId> = HashMap::new();

    let idents = db.idents();
    let mut start_states = HashMap::with_capacity(idents.len());
    for &ident in idents.iter() {
        let non_terminal = match db.term(ident) {
            Term::Terminal(_) => continue,
            Term::NonTerminal(nt) => nt,
        };
        let goal = db.intern_non_terminal(NonTerminalData::Goal { non_terminal });

        let mut root_item_set = BTreeSet::new();
        for production in db.production(goal) {
            // There should only be one but doesn't hurt to add them "all"
            root_item_set.insert(Item {
                non_terminal: goal,
                production,
                index: 0,
            });
        }
        let new_state = add_state(db, &mut states, &root_item_set);
        start_states.insert(ident, new_state);
    }

    let mut state_id = 0;
    while state_id < states.len() {
        let mut terms = BTreeSet::new();

        let state = &mut states[state_id];
        for (item, _) in &state.item_set {
            if let Some(next) = item.next() {
                terms.insert(next);
            }
        }

        for term in terms {
            let mut new_state: HashMap<_, HashSet<_>> = HashMap::new();
            for (id, (item, _)) in states[state_id].item_set.iter().enumerate() {
                if item.next() != Some(term) {
                    continue;
                }
                new_state
                    .entry(Item {
                        non_terminal: item.non_terminal,
                        production: item.production.clone(),
                        index: item.index + 1,
                    })
                    .or_default()
                    .insert(ItemIndex {
                        state: Lr0StateId(state_id),
                        item: id,
                    });
            }
            let new_item_set = new_state.keys().cloned().collect();
            let next_state_id = *state_lookup
                .entry(new_item_set)
                .or_insert_with_key(|new_item_set| add_state(db, &mut states, new_item_set));
            let next_state = &mut states[next_state_id.0];
            for (item, back_refs) in &mut next_state.item_set {
                if let Some(new_back_refs) = new_state.get(item) {
                    back_refs.extend(new_back_refs.iter().copied());
                }
            }
            match term {
                Term::NonTerminal(nt) => {
                    states[state_id].goto.insert(nt, next_state_id);
                }
                Term::Terminal(t) => {
                    states[state_id].actions.insert(t, next_state_id);
                }
            }
        }

        state_id += 1;
    }

    Lr0ParseTable {
        start_states,
        states,
    }
}

fn add_state(
    db: &dyn ParseTable,
    states: &mut Vec<Lr0State>,
    state: &BTreeSet<Item>,
) -> Lr0StateId {
    let new_id = Lr0StateId(states.len());
    states.push(Lr0State {
        item_set: closure(db, state, new_id),
        actions: HashMap::new(),
        goto: HashMap::new(),
    });
    new_id
}

fn closure(
    db: &dyn ParseTable,
    state: &BTreeSet<Item>,
    state_id: Lr0StateId,
) -> Vec<(Item, BTreeSet<ItemIndex>)> {
    let mut state: Vec<_> = state
        .iter()
        .map(|item| (item.clone(), BTreeSet::new()))
        .collect();

    let mut added = HashMap::new();

    let mut i = 0;
    while i < state.len() {
        let (item, _) = &state[i];
        let item_id = i;
        i += 1;

        let non_terminal = match item.next() {
            Some(Term::NonTerminal(nt)) => nt,
            _ => continue,
        };

        let start = *added
            .entry(non_terminal)
            .or_insert_with_key(|&non_terminal| {
                let start = state.len();
                state.extend(
                    db.production(non_terminal)
                        .into_iter()
                        .map(|p| (Item::new(non_terminal, p), BTreeSet::new())),
                );
                start
            });
        for (item, back_refs) in &mut state[start..] {
            if item.non_terminal != non_terminal {
                break;
            }
            back_refs.insert(ItemIndex {
                state: state_id,
                item: item_id,
            });
        }
    }
    state
}

fn parse_table(db: &dyn ParseTable) -> LrkParseTable {
    LrkParseTableBuilder::build(db)
}

struct LrkParseTableBuilder<'a> {
    db: &'a dyn ParseTable,
    lr0_parse_table: Lr0ParseTable,
}

impl<'a> LrkParseTableBuilder<'a> {
    fn build(db: &'a dyn ParseTable) -> LrkParseTable {
        let mut states = Vec::new();
        let mut builder = Self {
            db,
            lr0_parse_table: db.lr0_parse_table(),
        };

        let mut invalidated = Vec::new();
        let mut lr0_state_id = 0;
        while lr0_state_id < builder.lr0_parse_table.states.len() {
            let next_state = &builder.lr0_parse_table[Lr0StateId(lr0_state_id)];
            let conflicts = conflicts(next_state, lr0_state_id);
            let goto = next_state
                .goto
                .iter()
                .map(|(&nt, &id)| (nt, StateId(id.0)))
                .collect();

            let mut invalidate_state = |id: Lr0StateId| {
                if id.0 < lr0_state_id {
                    invalidated.push(id.0);
                }
            };

            let mut visited = HashSet::new();
            visited.insert(Lr0StateId(lr0_state_id));
            // This shouldn't loop forever because a split has ocurred each time
            // it returns, so at worst it will convert the entire graph into a
            // tree and then exit.
            let action = loop {
                let make_action =
                    builder.make_action(visited.clone(), conflicts.clone(), &mut invalidate_state);
                if let Some(action) = make_action {
                    break action;
                }
            };
            states.push(State { action, goto });
            lr0_state_id += 1
        }
        while let Some(lr0_state_id) = invalidated.pop() {
            let next_state = &builder.lr0_parse_table[Lr0StateId(lr0_state_id)];
            let conflicts = conflicts(next_state, lr0_state_id);
            let goto = next_state
                .goto
                .iter()
                .map(|(&nt, &id)| (nt, StateId(id.0)))
                .collect();

            let mut invalidate_state = |id: Lr0StateId| {
                if id.0 < lr0_state_id {
                    invalidated.push(id.0);
                }
            };

            let mut visited = HashSet::new();
            visited.insert(Lr0StateId(lr0_state_id));
            // This shouldn't loop forever because a split has ocurred each time
            // it returns, so at worst it will convert the entire graph into a
            // tree and then exit.
            let action = loop {
                let make_action =
                    builder.make_action(visited.clone(), conflicts.clone(), &mut invalidate_state);
                if let Some(action) = make_action {
                    break action;
                }
            };
            states[lr0_state_id] = State { action, goto };
        }
        LrkParseTable {
            start_states: builder
                .lr0_parse_table
                .start_states
                .into_iter()
                .map(|(k, v)| (k, StateId(v.0)))
                .collect(),
            states: states.into(),
        }
    }

    #[instrument(skip_all)]
    fn make_action(
        &mut self,
        mut visited: HashSet<Lr0StateId>,
        conflicts: HashMap<ConflictedAction, Vec<Ambiguity>>,
        invalidate_state: &mut impl FnMut(Lr0StateId),
    ) -> Option<Action> {
        assert!(!conflicts.is_empty());
        if conflicts.len() == 1 {
            return Some(
                conflicts
                    .into_iter()
                    .next()
                    .expect("conflicts contains 1 item")
                    .0
                    .into(),
            );
        }

        let mut split_info = HashMap::new();
        let mut potential_ambiguity = false;
        let mut next: HashMap<Terminal, HashMap<ConflictedAction, Vec<Ambiguity>>> = HashMap::new();

        // Extend ambiguities to next lookahead item
        for (action, mut ambiguities) in conflicts {
            while let Some(Ambiguity {
                location,
                transition,
                history,
                mut term_string,
            }) = ambiguities.pop()
            {
                trace!(%location, ?history, ?term_string, "Investigating ambiguity");
                if let Some(term) = term_string.terms.get(term_string.next_term).cloned() {
                    Arc::make_mut(&mut term_string).next_term += 1;
                    match term {
                        NormalTerm::Terminal(terminal) => {
                            trace!(terminal = %terminal.display(self.db), "Found terminal");
                            next.entry(terminal)
                                .or_default()
                                .entry(action.clone())
                                .or_default()
                                .push(Ambiguity {
                                    location,
                                    transition,
                                    history: history.clone(),
                                    term_string,
                                });
                        }
                        NormalTerm::NonTerminal(non_terminal) => {
                            trace!(non_terminal = %non_terminal.display(self.db), "Walking down into non-terminal");
                            ambiguities.extend(
                                self.db
                                    .normal_production(non_terminal)
                                    .into_iter()
                                    .map(|terms| {
                                        // This ambiguity already contains a loop or the new nonterminal has been seen before.
                                        let contains_loop = term_string.contains_loop
                                            || term_string
                                                .self_and_parents()
                                                .any(|p| p.non_terminal == Some(non_terminal));
                                        Ambiguity {
                                            location,
                                            transition,
                                            history: history.clone(),
                                            term_string: Arc::new(TermString {
                                                non_terminal: Some(non_terminal),
                                                terms,
                                                next_term: 0,
                                                parent: Some(term_string.clone()),
                                                contains_loop,
                                            }),
                                        }
                                    }),
                            )
                        }
                    }
                    continue;
                } else if let Some(parent) = &term_string.parent {
                    trace!("Walking up to parent");
                    ambiguities.push(Ambiguity {
                        location,
                        transition,
                        history,
                        term_string: parent.clone(),
                    });
                    continue;
                }
                // term_string is empty, so we must now walk the parse table.
                let mut lane_heads = HashMap::new();
                let mut lane_members = HashMap::new();
                potential_ambiguity |= self.item_lane_heads(
                    action.clone(),
                    location,
                    transition,
                    &mut split_info,
                    &mut lane_members,
                    &mut lane_heads,
                );
                visited.extend(lane_members.into_keys().map(|idx| idx.state));
                ambiguities.extend(lane_heads.into_iter().map(
                    |((location, transition), successors)| {
                        trace!(%location, "Walking parse table");
                        let item = &self.lr0_parse_table[location].0;
                        let mut history = history.clone();
                        history.extend(successors);
                        Ambiguity {
                            location,
                            transition,
                            history,
                            term_string: Arc::new(TermString {
                                non_terminal: None,
                                terms: item
                                    .production
                                    .iter()
                                    .map(|&term| term.into())
                                    .collect::<Vec<_>>()
                                    .into(),
                                next_term: item.index + 1,
                                parent: None,
                                contains_loop: false,
                            }),
                        }
                    },
                ));
            }
        }

        let mut splitting_occurred = false;
        for (state, split_table) in split_info {
            let mut splits: Vec<(HashSet<Term>, HashMap<NonTerminal, ConflictedAction>)> =
                Vec::new();
            for (term, actions) in split_table {
                let (terms, split_actions) = match splits.iter_mut().find(|(_, split)| {
                    actions.iter().all(|(nt, action)| {
                        split
                            .get(nt)
                            .map(|split_action| action == split_action)
                            .unwrap_or(true)
                    })
                }) {
                    Some(split) => split,
                    None => {
                        splits.push(Default::default());
                        splits.last_mut().unwrap()
                    }
                };
                terms.insert(term);
                split_actions.extend(actions);
            }
            if splits.len() <= 1 {
                continue;
            }
            splitting_occurred = true;
            debug!(splits = splits.len(), ?state, "Splitting states");
            let mut marks: HashMap<Lr0StateId, Vec<usize>> = HashMap::new();
            fn visit(
                parse_table: &Lr0ParseTable,
                visitable: &HashSet<Lr0StateId>,
                action: &mut impl FnMut(Lr0StateId),
                state: Lr0StateId,
            ) {
                if !visitable.contains(&state) {
                    return;
                }
                let mut visited = HashSet::new();
                visited.insert(state);
                let mut stack = vec![state];
                while let Some(state) = stack.pop() {
                    action(state);
                    for &next in parse_table[state]
                        .actions
                        .values()
                        .chain(parse_table[state].goto.values())
                    {
                        if visitable.contains(&next) && visited.insert(next) {
                            stack.push(next);
                        }
                    }
                }
            }
            for (mark, (terms, _)) in splits.iter().enumerate() {
                for next in terms {
                    let next_state = match next {
                        Term::Terminal(t) => self.lr0_parse_table[state].actions[t],
                        Term::NonTerminal(nt) => self.lr0_parse_table[state].goto[nt],
                    };
                    visit(
                        &self.lr0_parse_table,
                        &visited,
                        &mut |id| marks.entry(id).or_default().push(mark),
                        next_state,
                    );
                }
            }
            let mut state_id_map = HashMap::new();
            for &state in &visited {
                let Some(state_splits) = marks.get(&state) else {
                    continue;
                };
                let mut state_splits = state_splits.iter();

                // Reuse the existing state for the first split
                state_id_map.insert((state, *state_splits.next().unwrap()), state);

                for &split in state_splits {
                    state_id_map.insert(
                        (state, split),
                        Lr0StateId(self.lr0_parse_table.states.len()),
                    );
                    let new_state = self.lr0_parse_table[state].clone();
                    let new_state_id = Lr0StateId(self.lr0_parse_table.states.len());
                    // Add back references for all the targets not involved in
                    // this split as they won't get fixed up later.
                    std::iter::Iterator::chain(new_state.actions.values(), new_state.goto.values())
                        .filter(|target| !marks.contains_key(target))
                        .for_each(|&target| {
                            for (_, back_refs) in
                                &mut self.lr0_parse_table.states[target.0].item_set
                            {
                                back_refs.extend(
                                    back_refs
                                        .iter()
                                        .filter(|item_idx| item_idx.state == state)
                                        .map(|item_idx| ItemIndex {
                                            state: new_state_id,
                                            item: item_idx.item,
                                        })
                                        .collect::<Vec<_>>(),
                                )
                            }
                        });
                    self.lr0_parse_table.states.push(new_state);
                }
            }
            for (&(old_state_id, split), &new_state_id) in &state_id_map {
                let new_state = &mut self.lr0_parse_table.states[new_state_id.0];
                for (_, back_refs) in &mut new_state.item_set {
                    let old_back_refs = std::mem::take(back_refs);
                    back_refs.extend(old_back_refs.into_iter().filter_map(|back_ref| {
                        if marks.get(&back_ref.state).is_none() {
                            Some(back_ref)
                        } else {
                            state_id_map
                                .get(&(back_ref.state, split))
                                .map(|&new_id| ItemIndex {
                                    state: new_id,
                                    item: back_ref.item,
                                })
                        }
                    }));
                }
                for old_id in new_state
                    .actions
                    .values_mut()
                    .chain(new_state.goto.values_mut())
                {
                    if let Some(&new_id) = state_id_map.get(&(*old_id, split)) {
                        *old_id = new_id;
                    }
                }
                if old_state_id == new_state_id {
                    invalidate_state(old_state_id);
                }
            }
        }

        // FIXME: Maybe split states here, if two lookahead generating states
        // conflict in a way where splitting would help, could reduce the amount
        // of lookahead by increasing the number of states.

        if splitting_occurred {
            println!("{}", self.lr0_parse_table.display(self.db));
            None
        } else {
            if potential_ambiguity {
                panic!("Ambiguity!");
            }
            Some(Action::Ambiguous(
                next.into_iter()
                    .map(|(terminal, conflicts)| {
                        Some((
                            terminal,
                            self.make_action(visited.clone(), conflicts, invalidate_state)?,
                        ))
                    })
                    .collect::<Option<_>>()?,
            ))
        }
    }

    fn item_lane_heads(
        &mut self,
        action: ConflictedAction,
        location: ItemIndex,
        transition: Option<Term>,
        split_info: &mut HashMap<Lr0StateId, HashMap<Term, HashMap<NonTerminal, ConflictedAction>>>,
        visited: &mut HashMap<ItemIndex, u32>,
        output: &mut HashMap<(ItemIndex, Option<Term>), HashSet<ItemIndex>>,
    ) -> bool {
        let mut ret = false;
        trace!(
            action = %action.display(self.db),
            %location,
            transition = %transition.display(self.db),
            "Computing lane heads"
        );
        let (item, back_refs) = &self.lr0_parse_table[location];

        if let Some(next_state) = transition {
            let existing_action = split_info
                .entry(location.state)
                .or_default()
                .entry(next_state)
                .or_default()
                .entry(item.non_terminal);
            match existing_action {
                Entry::Occupied(entry) => {
                    if *entry.get() != action {
                        ret = true;
                    }
                }
                Entry::Vacant(entry) => {
                    entry.insert(action.clone());
                }
            }
        }

        let num_visits = visited.entry(location).or_default();
        *num_visits += 1;
        if item.index != 0 {
            // Allow the search to pass through nodes twice so that cycles get counted properly.
            if *num_visits <= 2 {
                for item_index in back_refs.clone() {
                    let transition = if item_index.state == location.state {
                        transition
                    } else {
                        self.lr0_parse_table[item_index].0.next()
                    };
                    ret |= self.item_lane_heads(
                        action.clone(),
                        item_index,
                        transition,
                        split_info,
                        visited,
                        output,
                    );
                }
            }
        } else {
            for &back_ref in back_refs {
                let transition = if back_ref.state == location.state {
                    transition
                } else {
                    self.lr0_parse_table[back_ref].0.next()
                };
                *visited.entry(back_ref).or_default() += 1;
                output
                    .entry((back_ref, transition))
                    .or_default()
                    .extend(visited.iter().filter(|(_, &v)| v > 0).map(|(&k, _)| k));
                *visited.entry(back_ref).or_default() -= 1;
            }
        }
        *visited.entry(location).or_default() -= 1;
        ret
    }
}

fn conflicts(
    next_state: &Lr0State,
    lr0_state_id: usize,
) -> HashMap<ConflictedAction, Vec<Ambiguity>> {
    let conflicts: HashMap<_, _> = next_state
        .item_set
        .iter()
        .enumerate()
        .filter_map(|(item_idx, (item, _))| {
            let conflict = match item.next() {
                Some(Term::NonTerminal(_)) => return None,
                Some(Term::Terminal(terminal)) => {
                    ConflictedAction::Shift(terminal, StateId(next_state.actions[&terminal].0))
                }
                None => ConflictedAction::Reduce(item.non_terminal, item.production.clone()),
            };
            let location = ItemIndex {
                state: Lr0StateId(lr0_state_id),
                item: item_idx,
            };
            let mut history = HashSet::new();
            history.insert(location);
            Some((
                conflict,
                vec![Ambiguity {
                    location,
                    transition: None,
                    history,
                    term_string: Arc::new(TermString {
                        non_terminal: None,
                        terms: item
                            .production
                            .iter()
                            .copied()
                            .map(NormalTerm::from)
                            .collect(),
                        next_term: item.index,
                        parent: None,
                        contains_loop: false,
                    }),
                }],
            ))
        })
        .collect();
    conflicts
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConflictedAction {
    Shift(Terminal, StateId),
    Reduce(NonTerminal, Arc<[Term]>),
}

impl<Db: ParseTable + ?Sized> DbDisplay<Db> for ConflictedAction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result {
        match self {
            ConflictedAction::Shift(terminal, id) => {
                writeln!(f, "Shift({}) -> {}", terminal.display(db), id)?;
            }
            ConflictedAction::Reduce(nt, ref terms) => {
                write!(f, "Reduce({} ->", nt.display(db))?;
                for term in &**terms {
                    write!(f, " {}", term.display(db))?;
                }
                writeln!(f, ")")?;
            }
        }
        Ok(())
    }
}

impl From<ConflictedAction> for Action {
    fn from(conflict: ConflictedAction) -> Self {
        match conflict {
            ConflictedAction::Shift(terminal, id) => Action::Shift(terminal, id),
            ConflictedAction::Reduce(non_terminal, production) => {
                Action::Reduce(non_terminal, production)
            }
        }
    }
}

#[derive(Debug, Clone)]
struct Ambiguity {
    location: ItemIndex,
    transition: Option<Term>,
    history: HashSet<ItemIndex>,
    term_string: Arc<TermString>,
}

#[derive(Debug, Clone)]
struct TermString {
    // Can be none at first as shifts may start halfway through the production
    non_terminal: Option<NormalNonTerminal>,
    terms: Arc<[NormalTerm]>,
    next_term: usize,
    parent: Option<Arc<TermString>>,
    contains_loop: bool,
}

impl TermString {
    fn self_and_parents(&self) -> impl Iterator<Item = &TermString> {
        std::iter::successors(Some(self), |s| s.parent.as_deref())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NormalNonTerminal {
    Original(NonTerminal),
    Minus(NonTerminal, Term),
}

impl<Db: ParseTable + ?Sized> DbDisplay<Db> for NormalNonTerminal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result {
        let (NormalNonTerminal::Original(non_terminal) | NormalNonTerminal::Minus(non_terminal, _)) =
            self;
        match db.lookup_intern_non_terminal(*non_terminal) {
            NonTerminalData::Goal { non_terminal } => {
                write!(f, "Goal({})", non_terminal.display(db))?;
            }
            NonTerminalData::Named { name, scope } => {
                write!(f, "{}#{}{{", db.lookup_intern_ident(name.ident), name.index)?;
                for (key, lower::Name { ident, index }) in scope.ident_map {
                    write!(
                        f,
                        "{}: {}#{}, ",
                        db.lookup_intern_ident(key),
                        db.lookup_intern_ident(ident),
                        index
                    )?;
                }
                write!(f, "}}")?;
            }
            NonTerminalData::Anonymous { .. } => write!(f, "#{}", non_terminal.0)?,
        }
        if let NormalNonTerminal::Minus(_, minus) = self {
            write!(f, "-{}", minus.display(db))?;
        }
        Ok(())
    }
}

impl From<NonTerminal> for NormalNonTerminal {
    fn from(nt: NonTerminal) -> Self {
        Self::Original(nt)
    }
}

impl NormalNonTerminal {
    fn base(&self) -> NonTerminal {
        match *self {
            NormalNonTerminal::Original(nt) => nt,
            NormalNonTerminal::Minus(nt, _) => nt,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NormalTerm {
    Terminal(Terminal),
    NonTerminal(NormalNonTerminal),
}

impl From<Term> for NormalTerm {
    fn from(t: Term) -> Self {
        match t {
            Term::Terminal(t) => Self::Terminal(t),
            Term::NonTerminal(nt) => Self::NonTerminal(nt.into()),
        }
    }
}

fn normal_production(
    db: &dyn ParseTable,
    non_terminal: NormalNonTerminal,
) -> OrdSet<Arc<[NormalTerm]>> {
    let original_production = db.production(non_terminal.base());
    match non_terminal {
        NormalNonTerminal::Original(non_terminal) => {
            if db.left_recursive(non_terminal) {
                // 1 - Moor00 5
                proper_left_corners(db, non_terminal)
                    .into_iter()
                    .filter(|term| !matches!(term, Term::NonTerminal(nt) if db.left_recursive(*nt)))
                    .map(|term| -> Arc<[_]> {
                        vec![
                            term.into(),
                            NormalTerm::NonTerminal(NormalNonTerminal::Minus(non_terminal, term)),
                        ]
                        .into()
                    })
                    .collect()
            } else {
                // 4 - Moor00 5
                original_production
                    .into_iter()
                    .map(|rule| -> Arc<[_]> {
                        rule.iter()
                            .map(|&term| term.into())
                            .collect::<Vec<_>>()
                            .into()
                    })
                    .collect()
            }
        }
        NormalNonTerminal::Minus(non_terminal, symbol) => {
            assert!(db.left_recursive(non_terminal));
            let mut rules = OrdSet::new();
            // 3 - Moor00 5
            rules.extend(
                db.production(non_terminal)
                    .into_iter()
                    .filter(|rule| rule.first() == Some(&symbol))
                    .map(|rule| -> Arc<[_]> {
                        rule.iter()
                            .skip(1)
                            .map(|&term| term.into())
                            .collect::<Vec<_>>()
                            .into()
                    }),
            );
            // 2 - Moor00 5
            rules.extend(
                proper_left_corners(db, non_terminal)
                    .into_iter()
                    .filter_map(|term| match term {
                        Term::NonTerminal(nt) if db.left_recursive(nt) => Some(nt),
                        _ => None,
                    })
                    .flat_map(|nt| {
                        db.production(nt)
                            .into_iter()
                            .filter(move |rule| rule.first() == Some(&symbol))
                            .map(move |rule| -> Arc<[_]> {
                                rule.iter()
                                    .skip(1)
                                    .map(|&term| term.into())
                                    .chain(std::iter::once(NormalTerm::NonTerminal(
                                        NormalNonTerminal::Minus(
                                            non_terminal,
                                            Term::NonTerminal(nt),
                                        ),
                                    )))
                                    .collect::<Vec<_>>()
                                    .into()
                            })
                    }),
            );
            rules
        }
    }
}

fn proper_left_corners(db: &dyn ParseTable, non_terminal: NonTerminal) -> HashSet<Term> {
    let mut left_corners = HashSet::new();
    let mut todo = vec![non_terminal];

    while let Some(nt) = todo.pop() {
        db.production(nt)
            .into_iter()
            .flat_map(|rule| rule.first().copied())
            .for_each(|term| {
                let new_term = left_corners.insert(term);
                match term {
                    Term::NonTerminal(next) if new_term && next != non_terminal => {
                        todo.push(next);
                    }
                    _ => {}
                }
            });
    }

    left_corners
}

fn left_recursive(db: &dyn ParseTable, non_terminal: NonTerminal) -> bool {
    proper_left_corners(db, non_terminal).contains(&Term::NonTerminal(non_terminal))
}
