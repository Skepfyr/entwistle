use std::{
    cell::RefCell,
    collections::{hash_map::Entry, BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    fmt::{self, Write as _},
    hash::Hash,
    ops::{ControlFlow, Index, IndexMut},
    rc::Rc,
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
    util::{
        look::{Look, LookMatcher, LookSet},
        primitives::StateID as NfaStateID,
    },
};
use tracing::{debug, debug_span, instrument, trace};

use self::{state_splitter::StateSplitter, term_string::TermString};
use crate::{
    diagnostics::{emit, Diagnostic},
    language::{Language, Rule},
    lower::{production, terminal_nfa, Alternative, NonTerminal, Term, TermKind, Terminal},
    util::DisplayWithDb,
    Db, Span,
};

mod state_splitter;
pub mod term_string;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LrkParseTable<'db> {
    pub goal: NonTerminal<'db>,
    pub states: Vec<State<'db>>,
}

impl<'db> DisplayWithDb for LrkParseTable<'db> {
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

impl<'db> Index<StateId> for LrkParseTable<'db> {
    type Output = State<'db>;

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
pub struct State<'db> {
    pub action: Action<'db>,
    pub goto: HashMap<NonTerminal<'db>, StateId>,
}

#[derive(Debug, Clone)]
pub enum Action<'db> {
    Lookahead {
        nfa: NFA,
        terminals: Vec<Terminal<'db>>,
        actions: Vec<Action<'db>>,
    },
    Shift(Terminal<'db>, StateId),
    Reduce(NonTerminal<'db>, Alternative<'db>),
    Ambiguous(Vec<Action<'db>>),
}

impl<'db> DisplayWithDb for Action<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        fn display(
            action: &Action,
            f: &mut fmt::Formatter<'_>,
            db: &dyn Db,
            lookahead: &mut Vec<String>,
        ) -> fmt::Result {
            match action {
                Action::Lookahead {
                    nfa: _,
                    terminals,
                    actions,
                } => {
                    for (terminal, action) in terminals.iter().zip(actions) {
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
                Action::Ambiguous(actions) => {
                    for action in actions {
                        display(action, f, db, lookahead)?;
                    }
                    Ok(())
                }
            }
        }
        display(self, f, db, &mut Vec::new())
    }
}

impl<'a, 'b> PartialEq<Action<'b>> for Action<'a> {
    fn eq(&self, other: &Action<'b>) -> bool {
        match (self, other) {
            (
                Self::Lookahead {
                    nfa: _,
                    terminals: l_regexes,
                    actions: l_actions,
                },
                Action::Lookahead {
                    nfa: _,
                    terminals: r_regexes,
                    actions: r_actions,
                },
            ) => l_regexes == r_regexes && l_actions == r_actions,
            (Self::Shift(l0, l1), Action::Shift(r0, r1)) => l0 == r0 && l1 == r1,
            (Self::Reduce(l0, l1), Action::Reduce(r0, r1)) => l0 == r0 && l1 == r1,
            _ => false,
        }
    }
}
impl<'db> Eq for Action<'db> {}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Item<'db> {
    pub non_terminal: NonTerminal<'db>,
    pub alternative: Alternative<'db>,
    pub index: usize,
}

impl<'db> Item<'db> {
    fn new(non_terminal: NonTerminal<'db>, alternative: Alternative<'db>) -> Self {
        Self {
            non_terminal,
            alternative,
            index: 0,
        }
    }

    fn next(&self, db: &'db dyn Db) -> Option<Term<'db>> {
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lr0ParseTable<'db> {
    pub goal: NonTerminal<'db>,
    pub states: Vec<Lr0State<'db>>,
}

impl<'db> DisplayWithDb for Lr0ParseTable<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        for (i, state) in self.states.iter().enumerate() {
            writeln!(f, "State {i}:")?;
            writeln!(indented(f).with_str("  "), "{}", state.display(db))?;
        }
        Ok(())
    }
}

impl<'db> Index<Lr0StateId> for Lr0ParseTable<'db> {
    type Output = Lr0State<'db>;

    fn index(&self, index: Lr0StateId) -> &Self::Output {
        &self.states[index.0]
    }
}

impl<'db> IndexMut<Lr0StateId> for Lr0ParseTable<'db> {
    fn index_mut(&mut self, index: Lr0StateId) -> &mut Self::Output {
        &mut self.states[index.0]
    }
}

impl<'db> Index<ItemIndex> for Lr0ParseTable<'db> {
    type Output = (Item<'db>, BTreeSet<ItemIndex>);

    fn index(&self, index: ItemIndex) -> &Self::Output {
        &self[index.state_id].item_set[index.item]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lr0State<'db> {
    pub item_set: Vec<(Item<'db>, BTreeSet<ItemIndex>)>,
    pub actions: BTreeMap<Terminal<'db>, Lr0StateId>,
    pub goto: BTreeMap<NonTerminal<'db>, Lr0StateId>,
}

impl<'db> DisplayWithDb for Lr0State<'db> {
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

#[salsa::tracked]
#[instrument(skip_all, fields(goal = %goal.display(db)))]
pub fn lr0_parse_table<'db>(
    db: &'db dyn Db,
    language: Language<'db>,
    goal: NonTerminal<'db>,
) -> Arc<Lr0ParseTable<'db>> {
    trace!("Generating LR(0) parse table");
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

    let parse_table = Lr0ParseTable { goal, states };
    trace!(parse_table = %parse_table.display(db), "Generated LR(0) parse table");
    Arc::new(parse_table)
}

fn add_state<'db>(
    db: &'db dyn Db,
    language: Language<'db>,
    states: &mut Vec<Lr0State<'db>>,
    state: &BTreeSet<Item<'db>>,
) -> Lr0StateId {
    let new_id = Lr0StateId(states.len());
    states.push(Lr0State {
        item_set: closure(db, language, state, new_id),
        actions: Default::default(),
        goto: Default::default(),
    });
    new_id
}

fn closure<'db>(
    db: &'db dyn Db,
    language: Language<'db>,
    state: &BTreeSet<Item<'db>>,
    state_id: Lr0StateId,
) -> Vec<(Item<'db>, BTreeSet<ItemIndex>)> {
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

#[instrument(skip_all, fields(goal = %goal.display(db)))]
pub fn parse_table<'db>(
    db: &'db dyn Db,
    language: Language<'db>,
    goal: Rule<'db>,
) -> LrkParseTable<'db> {
    let goal = NonTerminal::new_goal(db, goal);
    let lr0_parse_table = Lr0ParseTable::clone(&lr0_parse_table(db, language, goal));
    debug!(lr0_parse_table = %lr0_parse_table.display(db), "Generated LR(0) parse table");
    let lrk_parse_table = build_lrk_parse_table(db, language, lr0_parse_table);
    debug!(lrk_parse_table = %lrk_parse_table.display(db), "Generated LR(k) parse table");
    lrk_parse_table
}

fn build_lrk_parse_table<'db>(
    db: &'db dyn Db,
    language: Language<'db>,
    mut lr0_parse_table: Lr0ParseTable<'db>,
) -> LrkParseTable<'db> {
    let mut sccs = StronglyConnectedComponents::new(&lr0_parse_table);

    let mut states = Vec::new();

    let mut invalidated = (0..lr0_parse_table.states.len())
        .map(Lr0StateId)
        .collect::<VecDeque<_>>();
    while let Some(lr0_state_id) = invalidated.pop_front() {
        let next_state = &lr0_parse_table[lr0_state_id];
        let conflicts = conflicts(db, next_state, lr0_state_id, language);

        let mut invalidate_state = |id: Lr0StateId| {
            if !invalidated.contains(&id) {
                invalidated.push_back(id);
            }
        };

        // This shouldn't loop forever because a split has ocurred each time
        // it returns, so at worst it will convert the entire graph into a
        // tree and then exit.
        let action = loop {
            let span = debug_span!(
                "make_action",
                state = %lr0_state_id,
                conflicts = conflicts
                    .keys()
                    .map(|conflict| conflict.display(db))
                    .join(", "),
            );
            let _enter = span.enter();
            debug!(%sccs, "Making top-level action");
            let make_action = make_action(
                db,
                language,
                &mut lr0_parse_table,
                &mut sccs,
                lr0_state_id,
                conflicts.clone(),
                &mut invalidate_state,
            );
            if let Some(action) = make_action {
                break action;
            }
        };
        let goto = lr0_parse_table[lr0_state_id]
            .goto
            .iter()
            .map(|(nt, id)| (*nt, StateId(id.0)))
            .collect();
        if lr0_state_id.0 < states.len() {
            states[lr0_state_id.0] = State { action, goto };
        } else {
            assert!(
                lr0_state_id.0 == states.len(),
                "The queue enforces this grows one at a time"
            );
            states.push(State { action, goto });
        }
    }
    LrkParseTable {
        goal: lr0_parse_table.goal,
        states,
    }
}

fn make_action<'db>(
    db: &'db dyn Db,
    language: Language<'db>,
    lr0_parse_table: &mut Lr0ParseTable<'db>,
    sccs: &mut StronglyConnectedComponents,
    state: Lr0StateId,
    conflicts: HashMap<ConflictedAction<'db>, Ambiguity<'db>>,
    invalidate_state: &mut impl FnMut(Lr0StateId),
) -> Option<Action<'db>> {
    debug!("Making action");
    if conflicts.is_empty() {
        trace!("This state is broken as it has no actions");
        return Some(Action::Ambiguous(Vec::new()));
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

    let mut any_unfixable_conflicts = false;

    // Check if any ambiguities have term strings that will generate identical lookahead.
    // TODO: this could be more exhaustive.

    let identical_lookahead = conflicts
        .iter()
        .flat_map(|(action, ambiguity)| {
            ambiguity
                .locations
                .values()
                .map(|(_, term_string, _)| term_string)
                .flat_map(|term_string| {
                    term_string.locations.iter().flat_map(|location| {
                        term_string.parse_table[location.state]
                            .item_set
                            .iter()
                            .filter(|(item, _)| {
                                item.index == 0 && item.non_terminal.is_infinite(db, language)
                            })
                            .map(|(item, _)| item.non_terminal)
                    })
                })
                .map(move |nt| (nt, action))
        })
        .into_grouping_map()
        .collect::<HashSet<_>>();
    for (nt, actions) in identical_lookahead {
        if actions.len() <= 1 {
            continue;
        }
        any_unfixable_conflicts = true;
        emit(
            format!(
                "Conflict in state {} multiple actions have infinite non-terminal {} in lookahead:\n{}",
                state,
                nt.display(db),
                actions
                    .iter()
                    .map(|action| format!("{}", action.display(db)))
                    .format("\n")
            ),
            vec![(Span { start: 0, end: 0 }, None)],
        )
    }

    if any_unfixable_conflicts {
        return Some(Action::Ambiguous(
            conflicts.into_keys().map(|action| action.into()).collect(),
        ));
    }

    let Some(next) = StateSplitter::split_states(
        db,
        language,
        lr0_parse_table,
        sccs,
        conflicts,
        invalidate_state,
        state,
    ) else {
        debug!(lr0_parse_table = %lr0_parse_table.display(db), "Split");
        return None;
    };

    for (lookahead, next_conflicts) in &next {
        let span = debug_span!("common_loops", lookahead = %lookahead.display(db));
        let _enter = span.enter();
        let common_loops = next_conflicts.iter().fold(
            HashMap::<_, HashSet<_>>::new(),
            |mut common_loops, (action, ambiguities)| {
                let span = debug_span!("action", action = %action.display(db));
                let _enter = span.enter();
                for (ambiguity, history) in ambiguities {
                    trace!(ambiguity = %ambiguity.display(db), %history, "Finding loops");
                    // Add all the loops generated by the current term string.
                    ambiguity.term_string.loop_lengths(|loop_length| {
                        common_loops.entry(loop_length).or_default().insert(action);
                    });

                    // Add all the loops generated by the history.
                    history.loop_lengths(|loop_length| {
                        common_loops.entry(loop_length).or_default().insert(action);
                    });
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
            return Some(Action::Ambiguous(
                conflicts.into_keys().map(|action| action.into()).collect(),
            ));
        }
    }

    let terminals = next.keys().cloned().collect::<Vec<_>>();
    let nfa = build_nfa(db, language, &terminals);
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
                sccs,
                state,
                conflicts,
                invalidate_state,
            )
        })
        .collect::<Option<_>>()?;

    Some(Action::Lookahead {
        nfa,
        terminals,
        actions,
    })
}

fn next_terminals<'db>(
    db: &'db dyn Db,
    language: Language<'db>,
    lr0_parse_table: &Lr0ParseTable<'db>,
    conflicts: &HashMap<ConflictedAction<'db>, HashMap<Ambiguity<'db>, History>>,
) -> HashMap<Terminal<'db>, HashMap<ConflictedAction<'db>, HashMap<Ambiguity<'db>, History>>> {
    let mut next = HashMap::new();
    for (action, ambiguities) in conflicts {
        let mut visited = HashMap::new();
        for (ambiguity, history) in ambiguities {
            trace!(ambiguity = %ambiguity.display(db), %history, "Investigating ambiguity");

            let mut add_lane_head = |history: History| {
                trace!("Walking parse table");
                let item = &lr0_parse_table[history.location].0;
                let term_string = TermString::new(
                    db,
                    language,
                    Alternative::new(
                        db,
                        item.alternative.terms(db)[item.index + 1..].to_vec(),
                        item.alternative.negative_lookahead(db),
                    ),
                );
                let (can_be_empty, derivative) = term_string.next(db);
                add_derivative(
                    db,
                    derivative,
                    &action,
                    ambiguity.negative_lookahead.clone(),
                    history,
                    &mut next,
                );
                if can_be_empty {
                    ControlFlow::Continue(())
                } else {
                    ControlFlow::Break(())
                }
            };

            let (can_be_empty, derivative) = ambiguity.term_string.next(db);
            if can_be_empty {
                item_lane_heads(
                    db,
                    lr0_parse_table,
                    &mut add_lane_head,
                    Rc::new(history.clone()),
                    &mut visited,
                    &mut HashSet::new(),
                );
            }
            add_derivative(
                db,
                derivative,
                &action,
                ambiguity.negative_lookahead.clone(),
                history.clone(),
                &mut next,
            );
        }
    }
    next
}

#[instrument(level = "trace", skip_all, fields(location = %history.location))]
fn item_lane_heads<'db>(
    db: &'db dyn Db,
    lr0_parse_table: &Lr0ParseTable<'db>,
    add_lane_head: &mut impl FnMut(History) -> ControlFlow<()>,
    history: Rc<History>,
    histories: &mut HashMap<(bool, ItemIndex), Rc<History>>,
    mut visited: &mut HashSet<(bool, ItemIndex)>,
) {
    trace!("Computing lane heads");
    let (item, back_refs) = &lr0_parse_table[history.location];

    let is_lane_head = item.index == 0;
    for &back_ref in back_refs {
        if !visited.insert((is_lane_head, back_ref)) {
            continue;
        }
        let mut visited = scopeguard::guard(&mut visited, |visited| {
            visited.remove(&(is_lane_head, back_ref));
        });
        let entry = match histories.entry((is_lane_head, back_ref)) {
            Entry::Vacant(entry) => entry,
            Entry::Occupied(entry) => {
                entry
                    .get()
                    .merge_existing(history.clone().prepend_empty(back_ref));
                continue;
            }
        };
        let new_history = if is_lane_head {
            history.clone().prepend_lane_head(back_ref)
        } else {
            history.clone().prepend_empty(back_ref)
        };
        if !is_lane_head || add_lane_head(new_history.clone()) == ControlFlow::Continue(()) {
            let new_history = Rc::new(new_history);
            entry.insert(new_history.clone());
            item_lane_heads(
                db,
                lr0_parse_table,
                add_lane_head,
                new_history,
                histories,
                *visited,
            );
        }
    }
}

#[instrument(level = "trace", skip_all, fields(action = %action.display(db), history = %history))]
fn add_derivative<'db>(
    db: &'db dyn Db,
    derivative: HashMap<Terminal<'db>, HashSet<TermString<'db>>>,
    action: &ConflictedAction<'db>,
    negative_lookahead: Vec<TermString<'db>>,
    mut history: History,
    next: &mut HashMap<
        Terminal<'db>,
        HashMap<ConflictedAction<'db>, HashMap<Ambiguity<'db>, History>>,
    >,
) {
    history.terminals_yielded = history.terminals_yielded.iter().map(|i| *i + 1).collect();
    for (terminal, term_strings) in derivative {
        let negative_lookahead: Vec<_> = negative_lookahead
            .iter()
            .flat_map(|terms| terms.next(db).1.remove(&terminal))
            .flatten()
            .collect();
        if negative_lookahead
            .iter()
            .any(|term_string| term_string.next(db).0)
        {
            trace!("Dropping ambiguity because negative lookahead matched");
            continue;
        }
        let ambiguities = next
            .entry(terminal)
            .or_default()
            .entry(action.clone())
            .or_default();
        for term_string in term_strings {
            ambiguities
                .entry(Ambiguity {
                    location: history.location,
                    term_string,
                })
                .and_modify(|old_history| old_history.merge_head(history.clone()))
                .or_insert_with(|| history.clone());
        }
    }
}

fn conflicts<'db>(
    db: &'db dyn Db,
    next_state: &Lr0State<'db>,
    state_id: Lr0StateId,
    language: Language<'db>,
) -> HashMap<ConflictedAction<'db>, Ambiguity<'db>> {
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
                None => ConflictedAction::Reduce(item.non_terminal, item.alternative),
            };
            let location = ItemIndex {
                state_id,
                item: item_idx,
            };
            let mut locations = HashMap::new();
            locations.insert(
                location,
                (
                    History::new_lane_head(location),
                    TermString::new(
                        db,
                        language,
                        Alternative::new(
                            db,
                            item.alternative.terms(db)[item.index..].to_vec(),
                            item.alternative.negative_lookahead(db),
                        ),
                        Vec::new(),
                    ),
                ),
            );
            Some((conflict, Ambiguity { locations }))
        })
        .collect();
    conflicts
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConflictedAction<'db> {
    Shift(Terminal<'db>, StateId),
    Reduce(NonTerminal<'db>, Alternative<'db>),
}

impl<'db> DisplayWithDb for ConflictedAction<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        match self {
            ConflictedAction::Shift(terminal, id) => {
                write!(f, "Shift({}) -> {}", terminal.display(db), id)?;
            }
            ConflictedAction::Reduce(non_terminal, alternative) => {
                write!(
                    f,
                    "Reduce({} -> {})",
                    non_terminal.display(db),
                    alternative.display(db)
                )?;
            }
        }
        Ok(())
    }
}

impl<'db> From<ConflictedAction<'db>> for Action<'db> {
    fn from(conflict: ConflictedAction<'db>) -> Self {
        match conflict {
            ConflictedAction::Shift(terminal, id) => Action::Shift(terminal, id),
            ConflictedAction::Reduce(non_terminal, alternative) => {
                Action::Reduce(non_terminal, alternative)
            }
        }
    }
}

#[derive(Debug)]
struct Ambiguity<'db> {
    locations: HashMap<ItemIndex, (History, TermString<'db>)>,
}

impl<'db> DisplayWithDb for Ambiguity<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, _db: &dyn Db) -> fmt::Result {
        write!(f, "Ambiguity for {{{}}}", self.locations.keys().format(","),)
    }
}

#[derive(Debug, Clone)]
struct History {
    location: ItemIndex,
    terminals_yielded: BTreeSet<u32>,
    previous: RefCell<Vec<Rc<History>>>,
}

impl History {
    fn new_lane_head(location: ItemIndex) -> Self {
        let mut terminals_yielded = BTreeSet::new();
        terminals_yielded.insert(0);
        Self {
            location,
            terminals_yielded,
            previous: RefCell::new(Vec::new()),
        }
    }

    fn prepend_empty(self: Rc<Self>, location: ItemIndex) -> History {
        History {
            location,
            terminals_yielded: BTreeSet::new(),
            previous: RefCell::new(vec![self]),
        }
    }

    fn prepend_lane_head(self: Rc<Self>, location: ItemIndex) -> History {
        let mut terminals_yielded = BTreeSet::new();
        terminals_yielded.insert(0);
        History {
            location,
            terminals_yielded,
            previous: RefCell::new(vec![self]),
        }
    }

    fn merge_existing(&self, other: History) {
        assert_eq!(self.location, other.location);
        assert!(other.terminals_yielded.is_empty());
        self.previous
            .borrow_mut()
            .extend(other.previous.into_inner());
    }

    fn merge_head(&mut self, other: History) {
        assert_eq!(self.location, other.location);
        self.terminals_yielded.extend(other.terminals_yielded);
        self.previous.get_mut().extend(other.previous.into_inner());
    }

    fn loop_lengths(&self, mut action: impl FnMut(u32)) {
        fn loop_lengths(
            this: &History,
            loc: ItemIndex,
            mut counts: BTreeSet<u32>,
            action: &mut impl FnMut(u32),
        ) {
            if !this.terminals_yielded.is_empty() {
                let prev_counts = std::mem::take(&mut counts);
                for &terminals_yielded in &this.terminals_yielded {
                    counts.extend(prev_counts.iter().map(|x| x + terminals_yielded));
                }
            }
            if this.location == loc {
                for &count in &counts {
                    action(count);
                }
            }
            for prev in &**this.previous.borrow() {
                loop_lengths(prev, loc, counts.clone(), action);
            }
        }

        // The loop length is from the start of the last time we saw this item to
        // the *start* of this item.
        let loc = self.location;
        let mut counts = BTreeSet::new();
        counts.insert(0);
        for prev in &**self.previous.borrow() {
            loop_lengths(prev, loc, counts.clone(), &mut action);
        }
    }
}

impl fmt::Display for History {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.location)?;
        if !self.terminals_yielded.is_empty() {
            write!(f, "x{{{}}}", self.terminals_yielded.iter().format(","))?;
        }
        match self.previous.borrow().as_slice() {
            [] => {}
            [prev] => write!(f, " {}", prev)?,
            prev => write!(f, " [{}]", prev.iter().format(", "))?,
        }
        Ok(())
    }
}

fn build_nfa(db: &dyn Db, language: Language, terminals: &[Terminal]) -> NFA {
    let mut builder = NfaBuilder::new();
    let start = builder
        .add_union(Vec::with_capacity(terminals.len()))
        .unwrap();
    for terminal in terminals {
        let regex = terminal_nfa(db, language, terminal.clone());
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

/// Check if one of the two terminals matches a prefix of the other
#[salsa::tracked]
pub fn terminals_conflict<'db>(
    db: &'db dyn Db,
    language: Language<'db>,
    terminal_a: Terminal<'db>,
    terminal_b: Terminal<'db>,
) -> Result<(), Diagnostic> {
    if terminal_a == terminal_b {
        return Err(Diagnostic {
            message: format!("Terminal conflicts with itself: {}", terminal_a.display(db)),
            labels: vec![(Span { start: 0, end: 0 }, None)],
        });
    }

    let a = terminal_nfa(db, language, terminal_a.clone());
    let b = terminal_nfa(db, language, terminal_b.clone());

    // TODO: this is a hack around the fact that I can't work out how to deal
    // with unicode word boundaries as they're multi-byte.
    const UNICODE_LOOK: LookSet = LookSet {
        bits: Look::WordEndHalfUnicode.as_repr()
            | Look::WordEndUnicode.as_repr()
            | Look::WordStartHalfUnicode.as_repr()
            | Look::WordStartUnicode.as_repr()
            | Look::WordUnicode.as_repr()
            | Look::WordUnicodeNegate.as_repr(),
    };
    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    struct Pos {
        a: NfaStateID,
        b: NfaStateID,
        is_prev_char_word: bool,
        is_prev_char_newline: bool,
        look_set: u32,
    }

    let start = Pos {
        a: a.start_anchored(),
        b: b.start_anchored(),
        is_prev_char_word: false,
        is_prev_char_newline: false,
        look_set: LookSet::empty().bits,
    };
    let mut visited = HashSet::new();
    let mut to_check = vec![(start, vec![])];
    visited.insert(start);
    while let Some((pos, prefix)) = to_check.pop() {
        let a_state = a.state(pos.a);
        let b_state = b.state(pos.b);
        if let (NfaState::Match { .. }, NfaState::Match { .. }) = (a_state, b_state) {
            return Err(Diagnostic {
                message: format!(
                    "Ambiguous terminals {} and {}, both match the prefix {:?}",
                    terminal_a.display(db),
                    terminal_b.display(db),
                    String::from_utf8_lossy(&prefix),
                ),
                labels: vec![(Span { start: 0, end: 0 }, None)],
            });
        }
        match a_state {
            NfaState::ByteRange { .. }
            | NfaState::Sparse(_)
            | NfaState::Dense(_)
            | NfaState::Match { .. } => {}
            &NfaState::Look { look, next } => {
                let next = Pos {
                    a: next,
                    look_set: if look.as_repr() & UNICODE_LOOK.bits != 0 {
                        pos.look_set
                    } else {
                        pos.look_set | look.as_repr()
                    },
                    ..pos
                };
                if visited.insert(next) {
                    to_check.push((next, prefix.clone()));
                }
                continue;
            }
            NfaState::Union { alternates } => {
                for &alt in &**alternates {
                    let next = Pos { a: alt, ..pos };
                    if visited.insert(next) {
                        to_check.push((next, prefix.clone()));
                    }
                }
                continue;
            }
            &NfaState::BinaryUnion { alt1, alt2 } => {
                let next = Pos { a: alt1, ..pos };
                if visited.insert(next) {
                    to_check.push((next, prefix.clone()));
                }
                let next = Pos { a: alt2, ..pos };
                if visited.insert(next) {
                    to_check.push((next, prefix.clone()));
                }
                continue;
            }
            &NfaState::Capture { next, .. } => {
                let next = Pos { a: next, ..pos };
                if visited.insert(next) {
                    to_check.push((next, prefix.clone()));
                }
                continue;
            }
            NfaState::Fail => continue,
        }
        match b_state {
            NfaState::ByteRange { .. }
            | NfaState::Sparse(_)
            | NfaState::Dense(_)
            | NfaState::Match { .. } => {}
            &NfaState::Look { look, next } => {
                let next = Pos {
                    b: next,
                    look_set: if look.as_repr() & UNICODE_LOOK.bits != 0 {
                        pos.look_set
                    } else {
                        pos.look_set | look.as_repr()
                    },
                    ..pos
                };
                if visited.insert(next) {
                    to_check.push((next, prefix.clone()));
                }
                continue;
            }
            NfaState::Union { alternates } => {
                for &alt in &**alternates {
                    let next = Pos { b: alt, ..pos };
                    if visited.insert(next) {
                        to_check.push((next, prefix.clone()));
                    }
                }
                continue;
            }
            &NfaState::BinaryUnion { alt1, alt2 } => {
                let next = Pos { b: alt1, ..pos };
                if visited.insert(next) {
                    to_check.push((next, prefix.clone()));
                }
                let next = Pos { b: alt2, ..pos };
                if visited.insert(next) {
                    to_check.push((next, prefix.clone()));
                }
                continue;
            }
            &NfaState::Capture { next, .. } => {
                let next = Pos { b: next, ..pos };
                if visited.insert(next) {
                    to_check.push((next, prefix.clone()));
                }
                continue;
            }
            NfaState::Fail => continue,
        }
        for c in 0..=u8::MAX {
            let a_state = match a_state {
                NfaState::ByteRange { trans } => trans.matches_byte(c).then_some(trans.next),
                NfaState::Sparse(trans) => trans.matches_byte(c),
                NfaState::Dense(trans) => trans.matches_byte(c),
                NfaState::Match { .. } => Some(pos.a),
                NfaState::Look { .. }
                | NfaState::Union { .. }
                | NfaState::BinaryUnion { .. }
                | NfaState::Capture { .. }
                | NfaState::Fail => unreachable!(),
            };
            let b_state = match b_state {
                NfaState::ByteRange { trans } => trans.matches_byte(c).then_some(trans.next),
                NfaState::Sparse(trans) => trans.matches_byte(c),
                NfaState::Dense(trans) => trans.matches_byte(c),
                NfaState::Match { .. } => Some(pos.b),
                NfaState::Look { .. }
                | NfaState::Union { .. }
                | NfaState::BinaryUnion { .. }
                | NfaState::Capture { .. }
                | NfaState::Fail => unreachable!(),
            };
            let (a_state, b_state) = match (a_state, b_state) {
                (Some(a), Some(b)) => (a, b),
                _ => continue,
            };
            let mut prefix = prefix.clone();
            prefix.push(c);
            let look_matches = LookMatcher::new().matches_set(
                LookSet { bits: pos.look_set },
                &prefix,
                prefix.len() - 1,
            );
            if !look_matches {
                continue;
            }
            let next = Pos {
                a: a_state,
                b: b_state,
                is_prev_char_word: c == b'_' || c.is_ascii_alphanumeric(),
                is_prev_char_newline: c == b'\n',
                look_set: LookSet::empty().bits,
            };
            if visited.insert(next) {
                to_check.push((next, prefix));
            }
        }
    }
    Ok(())
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ComponentId(usize);

struct Component {
    states: HashSet<Lr0StateId>,
    forward_refs: HashSet<ComponentId>,
    backward_refs: HashSet<ComponentId>,
}

struct StronglyConnectedComponents {
    components: Vec<Component>,
    component_map: HashMap<Lr0StateId, ComponentId>,
}

impl fmt::Display for StronglyConnectedComponents {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        f.write_char('[')?;
        for component in &self.components {
            if component.states.len() == 1 {
                continue;
            }
            if first {
                first = false;
            } else {
                f.write_str(", ")?;
            }
            f.write_str("{")?;
            for (i, state) in component.states.iter().enumerate() {
                if i != 0 {
                    f.write_str(", ")?;
                }
                write!(f, "{}", state)?;
            }
            f.write_str("}")?;
        }
        f.write_char(']')?;
        Ok(())
    }
}

impl StronglyConnectedComponents {
    fn new(lr0_parse_table: &Lr0ParseTable) -> Self {
        let mut components = Vec::new();
        let mut component_map = HashMap::new();
        let mut stack = Vec::new();
        let mut indices = HashMap::new();
        let mut low_link = HashMap::new();
        let mut index = 0;

        for state_id in 0..lr0_parse_table.states.len() {
            let state_id = Lr0StateId(state_id);
            if !indices.contains_key(&state_id) {
                strong_connect(
                    lr0_parse_table,
                    state_id,
                    &mut index,
                    &mut stack,
                    &mut indices,
                    &mut low_link,
                    &mut components,
                    &mut component_map,
                );
            }
        }

        fn strong_connect(
            lr0_parse_table: &Lr0ParseTable,
            state_id: Lr0StateId,
            index: &mut u32,
            stack: &mut Vec<Lr0StateId>,
            indices: &mut HashMap<Lr0StateId, u32>,
            low_link: &mut HashMap<Lr0StateId, u32>,
            components: &mut Vec<HashSet<Lr0StateId>>,
            component_map: &mut HashMap<Lr0StateId, ComponentId>,
        ) {
            let state = &lr0_parse_table[state_id];
            indices.insert(state_id, *index);
            low_link.insert(state_id, *index);
            *index += 1;
            stack.push(state_id);
            for &next in state.goto.values().chain(state.actions.values()) {
                match indices.get(&next) {
                    None => {
                        strong_connect(
                            lr0_parse_table,
                            next,
                            index,
                            stack,
                            indices,
                            low_link,
                            components,
                            component_map,
                        );
                        low_link.insert(state_id, low_link[&state_id].min(low_link[&next]));
                    }
                    Some(next_index) if stack.contains(&next) => {
                        low_link.insert(state_id, low_link[&state_id].min(*next_index));
                    }
                    _ => (),
                }
            }
            if low_link[&state_id] == indices[&state_id] {
                let mut component = HashSet::new();
                loop {
                    let next = stack.pop().unwrap();
                    component.insert(next);
                    component_map.insert(next, ComponentId(components.len()));
                    if next == state_id {
                        break;
                    }
                }
                components.push(component);
            }
        }

        let components = components
            .into_iter()
            .enumerate()
            .map(|(i, states)| {
                let component_id = ComponentId(i);
                let mut forward_refs = HashSet::new();
                let mut backward_refs = HashSet::new();
                for state_id in states.iter().copied() {
                    let state = &lr0_parse_table[state_id];
                    for &next in state.goto.values().chain(state.actions.values()) {
                        let next_component = component_map[&next];
                        if next_component != component_id {
                            forward_refs.insert(next_component);
                        }
                    }
                    for (_, back_refs) in &state.item_set {
                        for back_ref in back_refs {
                            let prev_component = component_map[&back_ref.state_id];
                            if prev_component != component_id {
                                backward_refs.insert(prev_component);
                            }
                        }
                    }
                }
                Component {
                    states,
                    forward_refs,
                    backward_refs,
                }
            })
            .collect();

        Self {
            components,
            component_map,
        }
    }

    fn component(&self, state_id: Lr0StateId) -> ComponentId {
        self.component_map[&state_id]
    }

    fn states(&self, component: ComponentId) -> &HashSet<Lr0StateId> {
        &self.components[component.0].states
    }

    fn refs(&self, component: ComponentId) -> &HashSet<ComponentId> {
        &self.components[component.0].forward_refs
    }

    fn back_refs(&self, component: ComponentId) -> &HashSet<ComponentId> {
        &self.components[component.0].backward_refs
    }
}
