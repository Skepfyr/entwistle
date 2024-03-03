use std::{
    collections::{hash_map::Entry, BTreeMap, BTreeSet, HashMap, HashSet},
    fmt::{self, Write as _},
    hash::Hash,
    ops::Index,
    sync::Arc,
    vec,
};

use indenter::indented;
use itertools::Itertools;
use regex_automata::{
    nfa::thompson::{
        Builder as NfaBuilder, DenseTransitions, SparseTransitions, State as NfaState, Transition,
        NFA,
    },
    util::look::Look,
    PatternID,
};
use tracing::{debug, debug_span, trace};

use crate::{
    diagnostics::emit,
    language::{Language, Rule},
    lower::{production, terminal_nfa, Alternative, NonTerminal, Term, TermKind, Terminal},
    util::DisplayWithDb,
    Db, Span,
};

use self::term_string::TermString;

pub mod term_string;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LrkParseTable {
    pub goal: NonTerminal,
    pub states: Vec<State>,
}

impl DisplayWithDb for LrkParseTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        writeln!(f, "Goal: {}", self.goal.display(db))?;
        for (i, state) in self.states.iter().enumerate() {
            writeln!(f, "State {i}:")?;
            writeln!(f, "  Actions:")?;
            write!(indented(f).with_str("    "), "{}", state.action.display(db))?;
            writeln!(f, "  Goto:")?;
            for (nt, state) in &state.goto {
                writeln!(f, "    {} -> {}", nt.display(db), state)?;
            }
        }
        Ok(())
    }
}

impl Index<StateId> for LrkParseTable {
    type Output = State;

    fn index(&self, index: StateId) -> &Self::Output {
        &self.states[index.0]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StateId(usize);

impl StateId {
    pub const START: StateId = StateId(0);
}

impl fmt::Display for StateId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    pub action: Action,
    pub goto: HashMap<NonTerminal, StateId>,
}

#[derive(Debug, Clone)]
pub enum Action {
    Ambiguous {
        nfa: NFA,
        terminals: Vec<Terminal>,
        actions: Vec<Action>,
    },
    Shift(Terminal, StateId),
    Reduce(NonTerminal, Alternative),
}

impl DisplayWithDb for Action {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        fn display(
            action: &Action,
            f: &mut fmt::Formatter<'_>,
            db: &dyn Db,
            lookahead: &mut Vec<String>,
        ) -> fmt::Result {
            match action {
                Action::Ambiguous {
                    nfa: _,
                    terminals: regexes,
                    actions,
                } => {
                    for (terminal, action) in regexes.iter().zip(actions) {
                        lookahead.push(format!("{}", terminal.display(db)));
                        display(action, f, db, lookahead)?;
                        lookahead.pop();
                    }
                    Ok(())
                }
                Action::Shift(terminal, state) => {
                    for terminal in lookahead {
                        write!(f, "{terminal} ")?;
                    }
                    writeln!(f, ": Shift({}) -> {}", terminal.display(db), state)
                }
                Action::Reduce(non_terminal, alternative) => {
                    for terminal in lookahead {
                        write!(f, "{terminal} ")?;
                    }
                    writeln!(
                        f,
                        ": Reduce({} -> {})",
                        non_terminal.display(db),
                        alternative.display(db)
                    )
                }
            }
        }
        display(self, f, db, &mut Vec::new())
    }
}

impl PartialEq for Action {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Ambiguous {
                    nfa: _,
                    terminals: l_regexes,
                    actions: l_actions,
                },
                Self::Ambiguous {
                    nfa: _,
                    terminals: r_regexes,
                    actions: r_actions,
                },
            ) => l_regexes == r_regexes && l_actions == r_actions,
            (Self::Shift(l0, l1), Self::Shift(r0, r1)) => l0 == r0 && l1 == r1,
            (Self::Reduce(l0, l1), Self::Reduce(r0, r1)) => l0 == r0 && l1 == r1,
            _ => false,
        }
    }
}
impl Eq for Action {}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Item {
    pub non_terminal: NonTerminal,
    pub alternative: Alternative,
    pub index: usize,
}

impl Item {
    fn new(non_terminal: NonTerminal, alternative: Alternative) -> Self {
        Self {
            non_terminal,
            alternative,
            index: 0,
        }
    }

    fn next(&self, db: &dyn Db) -> Option<Term> {
        self.alternative.terms(db).get(self.index).cloned()
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
    state_id: Lr0StateId,
    item: usize,
}

impl fmt::Display for ItemIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.state_id, self.item)
    }
}

pub fn first_set(
    db: &dyn Db,
    language: Language,
    non_terminal: NonTerminal,
) -> (bool, HashSet<Terminal>) {
    production(db, language, non_terminal)
        .alternatives(db)
        .iter()
        .map(|alternative| alternative.terms(db).first())
        .fold(
            (false, HashSet::new()),
            |(contains_null, mut set), term| match term {
                Some(Term {
                    kind: TermKind::Terminal(terminal),
                    ..
                }) => {
                    set.insert(terminal.clone());
                    (contains_null, set)
                }
                Some(Term {
                    kind: TermKind::NonTerminal(nt),
                    ..
                }) if *nt != non_terminal => {
                    let other = first_set(db, language, *nt);
                    set.extend(other.1);
                    (contains_null | other.0, set)
                }
                Some(Term {
                    kind: TermKind::NonTerminal(_),
                    ..
                }) => (contains_null, set),
                None => (true, set),
            },
        )
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lr0ParseTable {
    pub goal: NonTerminal,
    pub states: Vec<Lr0State>,
}

impl DisplayWithDb for Lr0ParseTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        for (i, state) in self.states.iter().enumerate() {
            writeln!(f, "State {i}:")?;
            writeln!(indented(f).with_str("  "), "{}", state.display(db))?;
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
        &self[index.state_id].item_set[index.item]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lr0State {
    pub item_set: Vec<(Item, BTreeSet<ItemIndex>)>,
    pub actions: BTreeMap<Terminal, Lr0StateId>,
    pub goto: BTreeMap<NonTerminal, Lr0StateId>,
}

impl DisplayWithDb for Lr0State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        writeln!(f, "Items:")?;
        for (i, (item, backlinks)) in self.item_set.iter().enumerate() {
            write!(f, "  {:>2}: {} ->", i, item.non_terminal.display(db))?;
            for term in &item.alternative.terms(db)[..item.index] {
                write!(f, " {}", term.display(db))?;
            }
            write!(f, " .")?;
            for term in &item.alternative.terms(db)[item.index..] {
                write!(f, " {}", term.display(db))?;
            }
            if let Some(lookahead) = &item.alternative.negative_lookahead(db) {
                write!(f, "(!>>{})", lookahead.display(db))?;
            }
            writeln!(f)?;
            write!(f, "      Backlinks: {{")?;
            for (i, item) in backlinks.iter().enumerate() {
                if i != 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", item)?;
            }
            writeln!(f, "}}")?;
        }
        writeln!(f, "Actions:")?;
        for (t, state) in &self.actions {
            writeln!(f, "  {} -> {}", t.display(db), state)?;
        }
        for (nt, state) in &self.goto {
            writeln!(f, "  {} -> {}", nt.display(db), state)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ItemSet {
    items: Vec<(Item, BTreeSet<ItemIndex>)>,
}

#[salsa::tracked]
pub fn lr0_parse_table(db: &dyn Db, language: Language, goal: NonTerminal) -> Arc<Lr0ParseTable> {
    trace!(goal = %goal.display(db), "Generating LR(0) parse table");
    let mut states: Vec<Lr0State> = Vec::new();
    let mut state_lookup: HashMap<BTreeSet<Item>, Lr0StateId> = HashMap::new();

    let mut root_item_set = BTreeSet::new();
    for alternative in production(db, language, goal).alternatives(db) {
        // There should only be one but doesn't hurt to add them "all"
        root_item_set.insert(Item::new(goal, *alternative));
    }
    add_state(db, language, &mut states, &root_item_set);

    let mut state_id = 0;
    while state_id < states.len() {
        let mut terms = BTreeSet::new();

        let state = &mut states[state_id];
        for (item, _) in &state.item_set {
            if let Some(next) = item.next(db) {
                terms.insert(next.kind);
            }
        }

        for term in terms {
            let mut new_state: HashMap<_, HashSet<_>> = HashMap::new();
            for (id, (item, _)) in states[state_id].item_set.iter().enumerate() {
                if item.next(db).as_ref().map(|t| &t.kind) != Some(&term) {
                    continue;
                }
                new_state
                    .entry(Item {
                        non_terminal: item.non_terminal,
                        alternative: item.alternative,
                        index: item.index + 1,
                    })
                    .or_default()
                    .insert(ItemIndex {
                        state_id: Lr0StateId(state_id),
                        item: id,
                    });
            }
            let new_item_set = new_state.keys().cloned().collect();
            let next_state_id =
                *state_lookup
                    .entry(new_item_set)
                    .or_insert_with_key(|new_item_set| {
                        add_state(db, language, &mut states, new_item_set)
                    });
            let next_state = &mut states[next_state_id.0];
            for (item, back_refs) in &mut next_state.item_set {
                if let Some(new_back_refs) = new_state.get(item) {
                    back_refs.extend(new_back_refs.iter().copied());
                }
            }
            match term {
                TermKind::NonTerminal(nt) => {
                    states[state_id].goto.insert(nt, next_state_id);
                }
                TermKind::Terminal(t) => {
                    states[state_id].actions.insert(t, next_state_id);
                }
            }
        }

        state_id += 1;
    }

    Arc::new(Lr0ParseTable { goal, states })
}

fn add_state(
    db: &dyn Db,
    language: Language,
    states: &mut Vec<Lr0State>,
    state: &BTreeSet<Item>,
) -> Lr0StateId {
    let new_id = Lr0StateId(states.len());
    states.push(Lr0State {
        item_set: closure(db, language, state, new_id),
        actions: Default::default(),
        goto: Default::default(),
    });
    new_id
}

fn closure(
    db: &dyn Db,
    language: Language,
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

        let non_terminal = match item.next(db) {
            Some(Term {
                kind: TermKind::NonTerminal(nt),
                ..
            }) => nt,
            _ => continue,
        };

        let start = *added.entry(non_terminal).or_insert_with(|| {
            let start = state.len();
            state.extend(
                production(db, language, non_terminal)
                    .alternatives(db)
                    .iter()
                    .map(|p| (Item::new(non_terminal, *p), BTreeSet::new())),
            );
            start
        });
        for (item, back_refs) in &mut state[start..] {
            if item.non_terminal != non_terminal {
                break;
            }
            back_refs.insert(ItemIndex {
                state_id,
                item: item_id,
            });
        }
    }
    state
}

pub fn parse_table(db: &dyn Db, language: Language, goal: Rule) -> LrkParseTable {
    let goal = NonTerminal::new_goal(db, goal);
    let lr0_parse_table = Lr0ParseTable::clone(&lr0_parse_table(db, language, goal));
    debug!(lr0_parse_table = %lr0_parse_table.display(db), "Generated LR(0) parse table");
    build_lrk_parse_table(db, language, lr0_parse_table)
}

fn build_lrk_parse_table(
    db: &dyn Db,
    language: Language,
    mut lr0_parse_table: Lr0ParseTable,
) -> LrkParseTable {
    let mut states = Vec::new();

    let mut invalidated = Vec::new();
    let mut lr0_state_id = 0;
    while lr0_state_id < lr0_parse_table.states.len() {
        let next_state = &lr0_parse_table[Lr0StateId(lr0_state_id)];
        let conflicts = conflicts(db, next_state, lr0_state_id, language);

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
            let span = debug_span!(
                "make_action",
                state = lr0_state_id,
                conflicts = conflicts
                    .keys()
                    .map(|conflict| conflict.display(db))
                    .join(", ")
            );
            let _enter = span.enter();
            debug!("Making top-level action");
            let make_action = make_action(
                db,
                language,
                &mut lr0_parse_table,
                visited.clone(),
                conflicts.clone(),
                &mut invalidate_state,
            );
            if let Some(action) = make_action {
                break action;
            }
        };
        let goto = lr0_parse_table[Lr0StateId(lr0_state_id)]
            .goto
            .iter()
            .map(|(nt, id)| (*nt, StateId(id.0)))
            .collect();
        states.push(State { action, goto });
        lr0_state_id += 1
    }
    while let Some(lr0_state_id) = invalidated.pop() {
        let next_state = &lr0_parse_table[Lr0StateId(lr0_state_id)];
        let conflicts = conflicts(db, next_state, lr0_state_id, language);

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
            let span = debug_span!(
                "make_action",
                state = lr0_state_id,
                conflicts = conflicts
                    .keys()
                    .map(|conflict| conflict.display(db))
                    .join(", ")
            );
            let _enter = span.enter();
            debug!("Making top-level action");
            let make_action = make_action(
                db,
                language,
                &mut lr0_parse_table,
                visited.clone(),
                conflicts.clone(),
                &mut invalidate_state,
            );
            if let Some(action) = make_action {
                break action;
            }
        };
        let goto = lr0_parse_table[Lr0StateId(lr0_state_id)]
            .goto
            .iter()
            .map(|(nt, id)| (*nt, StateId(id.0)))
            .collect();
        states[lr0_state_id] = State { action, goto };
    }
    LrkParseTable {
        goal: lr0_parse_table.goal,
        states,
    }
}

fn make_action(
    db: &dyn Db,
    language: Language,
    lr0_parse_table: &mut Lr0ParseTable,
    mut visited: HashSet<Lr0StateId>,
    conflicts: HashMap<ConflictedAction, HashMap<Ambiguity, Arc<History>>>,
    invalidate_state: &mut impl FnMut(Lr0StateId),
) -> Option<Action> {
    debug!("Making action");
    if conflicts.is_empty() {
        trace!("This state is broken as it has no actions");
        return Some(Action::Reduce(
            NonTerminal::new_anonymous(
                db,
                Rule {
                    span: Span { start: 0, end: 0 },
                    alternatives: BTreeSet::new(),
                },
                None,
                BTreeMap::new(),
            ),
            Alternative::new(db, Span { start: 0, end: 0 }, Vec::new(), None),
        ));
    } else if conflicts.len() == 1 {
        return Some(
            conflicts
                .into_iter()
                .next()
                .expect("conflicts contains 1 item") // ICE
                .0
                .into(),
        );
    }
    let arbitrary_resolution: Action = conflicts
        .iter()
        .next()
        .expect("conflicts has at least one item")
        .0
        .clone()
        .into();

    let mut split_info = HashMap::new();
    let mut potential_ambiguities = HashSet::new();
    let mut next: HashMap<Terminal, HashMap<ConflictedAction, HashMap<Ambiguity, Arc<History>>>> =
        HashMap::new();

    // Extend ambiguities to next lookahead item
    for (action, ambiguities) in conflicts {
        let span = debug_span!("extend_ambiguities", action = %action.display(db));
        let _enter = span.enter();
        let mut pending = ambiguities.into_iter().collect::<Vec<_>>();
        let mut ambiguities: HashMap<
            Ambiguity,
            (bool, HashMap<Terminal, HashSet<TermString>>, Arc<History>),
        > = HashMap::new();
        let mut lane_members = HashMap::new();
        while let Some((ambiguity, history)) = pending.pop() {
            let (can_be_empty, _, existing_history) = ambiguities
                .entry(ambiguity.clone())
                .or_insert_with_key(|ambiguity| {
                    let (can_be_empty, derivative) = ambiguity.term_string.next(db);
                    (can_be_empty, derivative, History::new(ambiguity.location))
                });
            if *can_be_empty {
                // term_string is empty, so we must now walk the parse table.
                potential_ambiguities.extend(item_lane_heads(
                    db,
                    language,
                    lr0_parse_table,
                    action.clone(),
                    ambiguity.clone(),
                    &history,
                    &mut split_info,
                    &mut lane_members,
                    &mut pending,
                ));
            }
            Arc::make_mut(existing_history).merge(&history);
        }
        visited.extend(lane_members.into_keys().map(|(idx, _)| idx.state_id));
        for (ambiguity, (_, derivative, history)) in ambiguities {
            for (terminal, term_strings) in derivative {
                let new_action = action.with_lookahead(db, terminal.clone());
                if new_action.contains_finished_lookahead(db) {
                    trace!("Dropping ambiguity because negative lookahead matched");
                    continue;
                }
                let action_ambiguities = next
                    .entry(terminal)
                    .or_default()
                    .entry(new_action)
                    .or_default();
                for term_string in term_strings {
                    let next_history = Arc::make_mut(
                        action_ambiguities
                            .entry(Ambiguity {
                                term_string,
                                ..ambiguity.clone()
                            })
                            .and_modify(|_| {
                                panic!("Merging histories! This might not be hittable...")
                            })
                            .or_insert_with(|| History::new(ambiguity.location)),
                    );
                    next_history.prev.extend(history.prev.iter().cloned());
                    next_history
                        .terminals_yielded
                        .extend(history.terminals_yielded.iter().map(|i| *i + 1));
                }
            }
        }
    }

    let mut splitting_occurred = false;
    for (state, split_table) in split_info {
        let mut splits: Vec<(HashSet<TermKind>, HashMap<usize, HashSet<ConflictedAction>>)> =
            Vec::new();
        for (term, actions) in split_table {
            let Some(term) = term else { continue };
            let (terms, split_actions) = match splits.iter_mut().find(|(_, split)| {
                actions.iter().all(|(item, action)| {
                    split
                        .get(item)
                        .map(|split_action| {
                            action
                                .iter()
                                .any(|(action, _)| split_action.contains(action))
                        })
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
            for (item, action) in actions {
                split_actions
                    .entry(item)
                    .or_default()
                    .extend(action.into_iter().map(|(action, _)| action));
            }
        }
        if splits.len() <= 1 {
            continue;
        }
        splitting_occurred = true;
        debug!(splits = splits.len(), ?state, "Splitting states");
        trace!(splits = %SplitDisplay(&splits).display(db), "Split info");
        struct SplitDisplay<'a>(
            &'a [(HashSet<TermKind>, HashMap<usize, HashSet<ConflictedAction>>)],
        );
        impl<'a> DisplayWithDb for SplitDisplay<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
                for (terms, item_actions) in self.0 {
                    f.write_char('{')?;
                    for (i, term) in terms.iter().enumerate() {
                        if i != 0 {
                            f.write_char(',')?;
                        }
                        write!(f, "{}", term.display(db))?;
                    }
                    writeln!(f, "}}:")?;
                    for (item, actions) in item_actions {
                        write!(f, "  {}: ", item)?;
                        for (j, action) in actions.iter().enumerate() {
                            if j != 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{}", action.display(db))?;
                        }
                        writeln!(f)?;
                    }
                }

                Ok(())
            }
        }
        let mut marks: HashMap<Lr0StateId, HashSet<usize>> = HashMap::new();
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
                let next_state = match &next {
                    TermKind::Terminal(t) => lr0_parse_table[state].actions[t],
                    TermKind::NonTerminal(nt) => lr0_parse_table[state].goto[nt],
                };
                visit(
                    lr0_parse_table,
                    &visited,
                    &mut |id| {
                        marks.entry(id).or_default().insert(mark);
                    },
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
                state_id_map.insert((state, split), Lr0StateId(lr0_parse_table.states.len()));
                let new_state = lr0_parse_table[state].clone();
                let new_state_id = Lr0StateId(lr0_parse_table.states.len());
                // Add back references for all the targets not involved in
                // this split as they won't get fixed up later.
                std::iter::Iterator::chain(new_state.actions.values(), new_state.goto.values())
                    .filter(|target| !marks.contains_key(target))
                    .for_each(|&target| {
                        for (_, back_refs) in &mut lr0_parse_table.states[target.0].item_set {
                            back_refs.extend(
                                back_refs
                                    .iter()
                                    .filter(|item_idx| item_idx.state_id == state)
                                    .map(|item_idx| ItemIndex {
                                        state_id: new_state_id,
                                        item: item_idx.item,
                                    })
                                    .collect::<Vec<_>>(),
                            )
                        }
                    });
                lr0_parse_table.states.push(new_state);
            }
        }
        for (&(old_state_id, split), &new_state_id) in &state_id_map {
            let new_state = &mut lr0_parse_table.states[new_state_id.0];
            for (_, back_refs) in &mut new_state.item_set {
                let old_back_refs = std::mem::take(back_refs);
                back_refs.extend(old_back_refs.into_iter().filter_map(|back_ref| {
                    if marks.get(&back_ref.state_id).is_none() {
                        Some(back_ref)
                    } else {
                        state_id_map
                            .get(&(back_ref.state_id, split))
                            .map(|&new_id| ItemIndex {
                                state_id: new_id,
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
        debug!(lr0_parse_table = %lr0_parse_table.display(db), "Split");
        return None;
    }

    if !potential_ambiguities.is_empty() {
        debug!("Ambiguity detected");
        for ambiguity in potential_ambiguities {
            let string_for_conflict = |conflict: &ConflictedAction| match conflict {
                ConflictedAction::Shift(t, s) => format!(
                    "could continue to state {} and read this {}",
                    s,
                    t.display(db)
                ),
                ConflictedAction::Reduce(nt, _, _) => {
                    format!("might have just read a {}", nt.display(db))
                }
            };
            emit(
                format!("{}", ambiguity.display(db)),
                vec![
                    (
                        Span { start: 0, end: 0 },
                        Some(string_for_conflict(&ambiguity.conflict_a.0)),
                    ),
                    (
                        Span { start: 0, end: 0 },
                        Some(string_for_conflict(&ambiguity.conflict_b.0)),
                    ),
                ],
            );
        }
        // Pick an arbitrary action to resolve the ambiguity
        return Some(arbitrary_resolution);
    }

    let mut regexes = Vec::with_capacity(next.len());
    let mut terminals = Vec::with_capacity(next.len());
    for (terminal, conflicts) in &next {
        let common_loops = conflicts.iter().fold(
            HashMap::<_, HashSet<_>>::new(),
            |mut common_loops, (action, ambiguities)| {
                for (ambiguity, history) in ambiguities {
                    ambiguity.term_string.loop_lengths(|loop_length| {
                        common_loops.entry(loop_length).or_default().insert(action);
                    });
                    // Reset count to 0 because we don't know how far through the state we are,
                    // the loop length is from the start of the last time we saw this item to
                    // the *start* of this item.
                    let loc = history.location;
                    let mut to_investigate: Vec<_> = history
                        .prev
                        .iter()
                        .map(|history| (history.clone(), 0u32))
                        .collect();
                    while let Some((history, prev_count)) = to_investigate.pop() {
                        for &terminals_yielded in &history.terminals_yielded {
                            let count = terminals_yielded + prev_count;
                            if count > 0 && history.location == loc {
                                common_loops.entry(count).or_default().insert(action);
                            }
                            for prev in &history.prev {
                                to_investigate.push((prev.clone(), count));
                            }
                        }
                    }
                }
                common_loops
            },
        );
        if common_loops.values().any(|actions| actions.len() > 1) {
            for (i, actions) in common_loops
                .into_iter()
                .filter(|(_, actions)| actions.len() > 1)
            {
                emit(
                    format!("Ambiguity: infinite lookahead, looping every {i} terminals"),
                    actions
                        .into_iter()
                        .map(|action| {
                            (
                                Span { start: 0, end: 0 },
                                Some(format!("{}", action.display(db))),
                            )
                        })
                        .collect(),
                );
            }
            return Some(arbitrary_resolution);
        }
        regexes.push(terminal_nfa(db, language, terminal));
        terminals.push(terminal.clone());
    }

    let nfa = build_nfa(&terminals, &regexes);
    if !validate_nfa(&nfa) {
        // This early return does mean we don't spot some high-level ambiguities
        // with the grammar, but this kind of ambiguity frequently causes massive
        // combinatorial explosions as make_action enumerates the entire language.
        return Some(arbitrary_resolution);
    }

    let actions = next
        .into_iter()
        .map(|(terminal, conflicts)| {
            let tracing_span = debug_span!(
                "make_action",
                terminal = %terminal.display(db),
                conflicts = conflicts.keys().map(|conflict| conflict.display(db)).join(", ")
            );
            let _guard = tracing_span.enter();
            make_action(
                db,
                language,
                lr0_parse_table,
                visited.clone(),
                conflicts,
                invalidate_state,
            )
        })
        .collect::<Option<_>>()?;

    Some(Action::Ambiguous {
        nfa,
        terminals,
        actions,
    })
}

fn item_lane_heads(
    db: &dyn Db,
    language: Language,
    lr0_parse_table: &Lr0ParseTable,
    action: ConflictedAction,
    ambiguity: Ambiguity,
    history: &Arc<History>,
    split_info: &mut HashMap<
        Lr0StateId,
        HashMap<Option<TermKind>, HashMap<usize, Vec<(ConflictedAction, Arc<History>)>>>,
    >,
    visited: &mut HashMap<(ItemIndex, Option<TermKind>), u32>,
    ambiguities: &mut Vec<(Ambiguity, Arc<History>)>,
) -> HashSet<AmbiguitySource> {
    trace!(action = %action.display(db), ambiguity = %ambiguity.display(db), "Computing lane heads");
    let (item, back_refs) = &lr0_parse_table[ambiguity.location];

    let num_visits = visited
        .entry((ambiguity.location, ambiguity.transition.clone()))
        .or_default();
    // Allow the search to pass through nodes twice so that cycles get counted properly.
    if *num_visits >= 2 {
        return HashSet::new();
    }
    *num_visits += 1;

    let mut ret = HashSet::new();
    let existing_action = split_info
        .entry(ambiguity.location.state_id)
        .or_default()
        .entry(ambiguity.transition.clone())
        .or_default()
        .entry(ambiguity.location.item);
    match existing_action {
        Entry::Occupied(mut entry) => {
            if entry
                .get()
                .iter()
                .all(|(old_action, _)| *old_action != action)
            {
                ret.extend(entry.get().iter().cloned().map(|(conflict_b, b_history)| {
                    AmbiguitySource {
                        location: ambiguity.location,
                        transition: ambiguity.transition.clone(),
                        non_terminal: item.non_terminal,
                        conflict_a: (action.clone(), history.clone()),
                        conflict_b: (conflict_b, b_history),
                    }
                }));
                entry.get_mut().push((action.clone(), history.clone()));
            }
        }
        Entry::Vacant(entry) => {
            entry.insert(vec![(action.clone(), history.clone())]);
        }
    }

    if item.index != 0 {
        for &item_index in back_refs {
            let transition = if item_index.state_id == ambiguity.location.state_id {
                ambiguity.transition.clone()
            } else {
                lr0_parse_table[item_index]
                    .0
                    .next(db)
                    .as_ref()
                    .map(|t| t.kind.clone())
            };
            ret.extend(item_lane_heads(
                db,
                language,
                lr0_parse_table,
                action.clone(),
                Ambiguity {
                    location: item_index,
                    transition,
                    ..ambiguity.clone()
                },
                history,
                split_info,
                visited,
                ambiguities,
            ));
        }
    } else {
        for &back_ref in back_refs {
            let transition = if back_ref.state_id == ambiguity.location.state_id {
                ambiguity.transition.clone()
            } else {
                lr0_parse_table[back_ref]
                    .0
                    .next(db)
                    .as_ref()
                    .map(|t| t.kind.clone())
            };
            trace!(%back_ref, "Walking parse table");
            let item = &lr0_parse_table[back_ref].0;
            let mut new_history = History::new(back_ref);
            Arc::make_mut(&mut new_history).prev.push(history.clone());
            ambiguities.push((
                Ambiguity {
                    location: back_ref,
                    transition: transition.clone(),
                    term_string: TermString::new(
                        db,
                        language,
                        item.alternative.terms(db)[item.index + 1..].to_vec(),
                    ),
                },
                new_history,
            ));
        }
    }
    ret
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct AmbiguitySource {
    location: ItemIndex,
    transition: Option<TermKind>,
    non_terminal: NonTerminal,
    conflict_a: (ConflictedAction, Arc<History>),
    conflict_b: (ConflictedAction, Arc<History>),
}

impl DisplayWithDb for AmbiguitySource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        write!(
            f,
            "Ambiguity for {} and {} ",
            self.conflict_a.0.display(db),
            self.conflict_b.0.display(db),
        )?;
        write!(
            f,
            "in {} for non-terminal {}",
            self.location,
            self.non_terminal.display(db),
        )?;
        match &self.transition {
            Some(transition) => writeln!(f, " and transition {}", transition.display(db)),
            None => writeln!(f),
        }?;
        writeln!(
            f,
            "history: {} and {}",
            self.conflict_a.1, self.conflict_b.1,
        )?;
        Ok(())
    }
}

fn conflicts(
    db: &dyn Db,
    next_state: &Lr0State,
    lr0_state_id: usize,
    language: Language,
) -> HashMap<ConflictedAction, HashMap<Ambiguity, Arc<History>>> {
    let conflicts: HashMap<_, _> = next_state
        .item_set
        .iter()
        .enumerate()
        .filter_map(|(item_idx, (item, _))| {
            let conflict = match item.next(db) {
                Some(Term {
                    kind: TermKind::NonTerminal(_),
                    ..
                }) => return None,
                Some(Term {
                    kind: TermKind::Terminal(terminal),
                    ..
                }) => {
                    let next_state = StateId(next_state.actions[&terminal].0);
                    ConflictedAction::Shift(terminal, next_state)
                }
                None => {
                    let remaining_negative_lookahead: Vec<_> =
                        match item.alternative.negative_lookahead(db) {
                            Some(negative_lookahead) => vec![TermString::new(
                                db,
                                language,
                                vec![Term {
                                    kind: TermKind::NonTerminal(negative_lookahead),
                                    silent: false,
                                }],
                            )],
                            None => Vec::new(),
                        };

                    ConflictedAction::Reduce(
                        item.non_terminal,
                        item.alternative,
                        remaining_negative_lookahead,
                    )
                }
            };
            if conflict.contains_finished_lookahead(db) {
                // If negative lookahead is finished then this action doesn't exist.
                return None;
            }
            let location = ItemIndex {
                state_id: Lr0StateId(lr0_state_id),
                item: item_idx,
            };
            let mut ambiguities = HashMap::new();
            ambiguities.insert(
                Ambiguity {
                    location,
                    transition: None,
                    term_string: TermString::new(
                        db,
                        language,
                        item.alternative.terms(db)[item.index..].to_vec(),
                    ),
                },
                History::new(location),
            );
            Some((conflict, ambiguities))
        })
        .collect();
    conflicts
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConflictedAction {
    Shift(Terminal, StateId),
    Reduce(NonTerminal, Alternative, Vec<TermString>),
}

impl ConflictedAction {
    fn with_lookahead(&self, db: &dyn Db, terminal: Terminal) -> ConflictedAction {
        match self {
            ConflictedAction::Reduce(non_terminal, alternative, remaining_negative_lookahead) => {
                let new_negative_lookahead = remaining_negative_lookahead
                    .iter()
                    .filter_map(|term_string| term_string.clone().next(db).1.remove(&terminal))
                    .flatten()
                    .collect();
                ConflictedAction::Reduce(*non_terminal, *alternative, new_negative_lookahead)
            }
            other => other.clone(),
        }
    }

    fn contains_finished_lookahead(&self, db: &dyn Db) -> bool {
        match self {
            ConflictedAction::Shift(_, _) => false,
            ConflictedAction::Reduce(_, _, remaining_negative_lookahead) => {
                remaining_negative_lookahead
                    .iter()
                    .any(|term_string| term_string.next(db).0)
            }
        }
    }
}

impl DisplayWithDb for ConflictedAction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        match self {
            ConflictedAction::Shift(terminal, id) => {
                write!(f, "Shift({}) -> {}", terminal.display(db), id)?;
            }
            ConflictedAction::Reduce(non_terminal, alternative, remaining_negative_lookahead) => {
                write!(
                    f,
                    "Reduce({} -> {}",
                    non_terminal.display(db),
                    alternative.display(db)
                )?;
                for lookahead in remaining_negative_lookahead {
                    write!(f, " (!>> {})", lookahead.display(db))?;
                }
                write!(f, ")")?;
            }
        }
        Ok(())
    }
}

impl From<ConflictedAction> for Action {
    fn from(conflict: ConflictedAction) -> Self {
        match conflict {
            ConflictedAction::Shift(terminal, id) => Action::Shift(terminal, id),
            ConflictedAction::Reduce(non_terminal, alternative, _) => {
                Action::Reduce(non_terminal, alternative)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Ambiguity {
    location: ItemIndex,
    transition: Option<TermKind>,
    term_string: TermString,
}

impl DisplayWithDb for Ambiguity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        let transition = self.transition.as_ref().map(|t| t.display(db));
        let transition = match transition {
            Some(t) => format!("Some({})", t),
            None => "None".to_string(),
        };
        write!(
            f,
            "Ambiguity for {} ({})",
            transition,
            self.term_string.display(db)
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct History {
    location: ItemIndex,
    terminals_yielded: BTreeSet<u32>,
    prev: Vec<Arc<History>>,
}

impl History {
    fn new(location: ItemIndex) -> Arc<Self> {
        let mut terminals_yielded = BTreeSet::new();
        terminals_yielded.insert(0);
        Arc::new(Self {
            location,
            terminals_yielded,
            prev: Vec::new(),
        })
    }

    fn merge(&mut self, other: &History) {
        assert_eq!(self.location, other.location);
        self.terminals_yielded
            .extend(other.terminals_yielded.iter().copied());
        self.prev.extend(other.prev.iter().cloned());
    }
}

impl fmt::Display for History {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}x{} [{}]",
            self.location,
            self.terminals_yielded.iter().format(","),
            self.prev.iter().format(", ")
        )
    }
}

fn build_nfa(terminals: &[Terminal], regexes: &[NFA]) -> NFA {
    let mut builder = NfaBuilder::new();
    let start = builder
        .add_union(Vec::with_capacity(terminals.len()))
        .unwrap();
    for regex in regexes {
        builder.start_pattern().unwrap();
        let pattern_start = builder
            .add_capture_start(regex_automata::util::primitives::StateID::MAX, 0, None)
            .unwrap();
        builder.patch(start, pattern_start).unwrap();

        let mut id_map = HashMap::new();
        id_map.insert(regex.start_anchored(), pattern_start);
        let mut to_add = vec![regex.start_anchored()];
        while let Some(id) = to_add.pop() {
            let new = match regex.state(id) {
                NfaState::ByteRange { trans } => {
                    let next = *id_map.entry(trans.next).or_insert_with_key(|id| {
                        to_add.push(*id);
                        builder.add_empty().unwrap()
                    });
                    builder
                        .add_range(Transition {
                            start: trans.start,
                            end: trans.end,
                            next,
                        })
                        .unwrap()
                }
                NfaState::Sparse(SparseTransitions { transitions }) => {
                    let transitions = transitions
                        .iter()
                        .map(|trans| Transition {
                            start: trans.start,
                            end: trans.end,
                            next: *id_map.entry(trans.next).or_insert_with_key(|id| {
                                to_add.push(*id);
                                builder.add_empty().unwrap()
                            }),
                        })
                        .collect();
                    builder.add_sparse(transitions).unwrap()
                }
                NfaState::Dense(DenseTransitions { transitions }) => {
                    let transitions = transitions
                        .iter()
                        .enumerate()
                        .map(|(i, next)| Transition {
                            start: i.try_into().unwrap(),
                            end: i.try_into().unwrap(),
                            next: *id_map.entry(*next).or_insert_with_key(|id| {
                                to_add.push(*id);
                                builder.add_empty().unwrap()
                            }),
                        })
                        .collect();
                    builder.add_sparse(transitions).unwrap()
                }
                NfaState::Look { look, next } => {
                    let next = *id_map.entry(*next).or_insert_with_key(|id| {
                        to_add.push(*id);
                        builder.add_empty().unwrap()
                    });
                    builder.add_look(next, *look).unwrap()
                }
                NfaState::Union { alternates } => {
                    let alternates = alternates
                        .iter()
                        .map(|alt| {
                            *id_map.entry(*alt).or_insert_with_key(|id| {
                                to_add.push(*id);
                                builder.add_empty().unwrap()
                            })
                        })
                        .collect();
                    builder.add_union(alternates).unwrap()
                }
                NfaState::BinaryUnion { alt1, alt2 } => {
                    let alternates = [alt1, alt2]
                        .into_iter()
                        .map(|alt| {
                            *id_map.entry(*alt).or_insert_with_key(|id| {
                                to_add.push(*id);
                                builder.add_empty().unwrap()
                            })
                        })
                        .collect();
                    builder.add_union(alternates).unwrap()
                }
                // Ignore capture groups because we only care about whether there's a match.
                NfaState::Capture {
                    next,
                    pattern_id: _,
                    group_index: _,
                    slot: _,
                } => *id_map.entry(*next).or_insert_with_key(|id| {
                    to_add.push(*id);
                    builder.add_empty().unwrap()
                }),
                NfaState::Fail => builder.add_fail().unwrap(),
                NfaState::Match { pattern_id: _ } => {
                    let match_state = builder.add_match().unwrap();
                    builder.add_capture_end(match_state, 0).unwrap()
                }
            };
            builder.patch(id_map[&id], new).unwrap();
        }

        builder.finish_pattern(pattern_start).unwrap();
    }
    builder.build(start, start).unwrap()
}

/// Check if any of the regexes are prefixes of any of the other regexes.
#[must_use]
fn validate_nfa(nfa: &NFA) -> bool {
    let mut valid = true;
    let mut start = BTreeSet::new();
    start.insert(nfa.start_anchored());
    let mut to_visit = vec![(start, None::<(PatternID, Vec<u8>)>, Vec::new())];
    let mut visited = HashSet::new();
    while let Some((mut states, mut new_colour, string)) = to_visit.pop() {
        loop {
            let mut to_add = Vec::new();
            for &id in &states {
                match nfa.state(id) {
                    &NfaState::Look { look, next } => {
                        // This is overzealous and will flag word boundaries etc as
                        // clashing when they actually aren't.
                        if look != Look::End {
                            to_add.push(next);
                        }
                    }
                    NfaState::Union { alternates } => to_add.extend(alternates.iter().copied()),
                    &NfaState::BinaryUnion { alt1, alt2 } => {
                        to_add.push(alt1);
                        to_add.push(alt2);
                    }
                    &NfaState::Capture { next, .. } => to_add.push(next),
                    NfaState::ByteRange { .. }
                    | NfaState::Sparse(_)
                    | NfaState::Dense(_)
                    | NfaState::Fail
                    | NfaState::Match { .. } => {}
                }
            }
            let mut modified = false;
            for state in to_add {
                modified |= states.insert(state);
            }
            if !modified {
                break;
            }
        }
        if !visited.insert(states.clone()) {
            continue;
        }
        let mut intrinsic_colour: Option<PatternID> = None;
        for &state in &states {
            if let &NfaState::Match {
                pattern_id: this_colour,
            } = nfa.state(state)
            {
                if let Some(other_colour) = intrinsic_colour {
                    if other_colour != this_colour {
                        valid = false;
                        emit(
                            format!(
                                "Two tokens match the string {}",
                                String::from_utf8_lossy(&string)
                            ),
                            vec![
                                (Span { start: 0, end: 0 }, None),
                                (Span { start: 0, end: 0 }, None),
                            ],
                        );
                    }
                } else {
                    intrinsic_colour = Some(this_colour);
                }
            }
        }
        if let (Some(intrinsic_colour), Some((new_colour, prefix))) =
            (intrinsic_colour, &new_colour)
        {
            if *new_colour != intrinsic_colour {
                valid = false;
                emit(
                    "Tokens conflict as one matches the prefix of the other",
                    vec![
                        (
                            Span { start: 0, end: 0 },
                            Some(format!(
                                "matches the string {:?}",
                                String::from_utf8_lossy(&string)
                            )),
                        ),
                        (
                            Span { start: 0, end: 0 },
                            Some(format!(
                                "matches the prefix {:?}",
                                String::from_utf8_lossy(prefix)
                            )),
                        ),
                    ],
                );
            }
        }
        new_colour = new_colour.or_else(|| intrinsic_colour.map(|c| (c, string.clone())));
        for i in 0..=u8::MAX {
            let next_states: BTreeSet<_> = states
                .iter()
                .flat_map(|id| match nfa.state(*id) {
                    NfaState::ByteRange { trans } => trans.matches_byte(i).then_some(trans.next),
                    NfaState::Sparse(trans) => trans.matches_byte(i),
                    NfaState::Dense(trans) => trans.matches_byte(i),
                    NfaState::Look { .. }
                    | NfaState::Union { .. }
                    | NfaState::BinaryUnion { .. }
                    | NfaState::Capture { .. }
                    | NfaState::Fail
                    | NfaState::Match { .. } => None,
                })
                .collect();
            if !next_states.is_empty() {
                let mut prefix = string.clone();
                prefix.push(i);
                to_visit.push((next_states, new_colour.clone(), prefix));
            }
        }
    }
    valid
}
