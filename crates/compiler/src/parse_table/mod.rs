use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    fmt::{self, Write as _},
    hash::Hash,
    ops::{ControlFlow, Index, IndexMut},
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

use crate::{
    diagnostics::{emit, emit_diagnostic, Diagnostic},
    language::{Language, Rule},
    lower::{production, terminal_nfa, Alternative, NonTerminal, Term, TermKind, Terminal},
    util::DisplayWithDb,
    Db, Span,
};

use self::term_string::TermString;

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
    Ambiguous {
        nfa: NFA,
        terminals: Vec<Terminal<'db>>,
        actions: Vec<Action<'db>>,
    },
    Shift(Terminal<'db>, StateId),
    Reduce(NonTerminal<'db>, Alternative<'db>),
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

impl<'a, 'b> PartialEq<Action<'b>> for Action<'a> {
    fn eq(&self, other: &Action<'b>) -> bool {
        match (self, other) {
            (
                Self::Ambiguous {
                    nfa: _,
                    terminals: l_regexes,
                    actions: l_actions,
                },
                Action::Ambiguous {
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

pub fn first_set<'db>(
    db: &'db dyn Db,
    language: Language<'db>,
    non_terminal: NonTerminal<'db>,
) -> (bool, HashSet<Terminal<'db>>) {
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
    conflicts: HashMap<ConflictedAction<'db>, HashMap<Ambiguity<'db>, History>>,
    invalidate_state: &mut impl FnMut(Lr0StateId),
) -> Option<Action<'db>> {
    debug!("Making action");
    if conflicts.is_empty() {
        trace!("This state is broken as it has no actions");
        return Some(Action::Reduce(
            NonTerminal::new_anonymous(
                db,
                language,
                Rule {
                    span: Span { start: 0, end: 0 },
                    alternatives: BTreeSet::new(),
                },
                None,
                BTreeMap::new(),
            ),
            Alternative::new(db, Vec::new(), None),
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

    let mut any_unfixable_conflicts = false;

    // Check if any ambiguities have term strings that will generate identical lookahead.
    // TODO: this could be more exhaustive.

    let identical_lookahead = conflicts
        .iter()
        .flat_map(|(action, ambiguities)| {
            ambiguities
                .keys()
                .flat_map(|ambiguity| {
                    let term_string = &ambiguity.term_string;
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
        return Some(arbitrary_resolution);
    }

    let next = ConflictDifferentiator::next_terminals(db, language, lr0_parse_table, conflicts);

    if StateSplitter::split_states(
        db,
        language,
        lr0_parse_table,
        sccs,
        invalidate_state,
        state,
        &next,
    ) {
        debug!(lr0_parse_table = %lr0_parse_table.display(db), "Split");
        return None;
    }

    for (lookahead, conflicts) in &next {
        let span = debug_span!("common_loops", lookahead = %lookahead.display(db));
        let _enter = span.enter();
        let common_loops = conflicts.iter().fold(
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
            return Some(arbitrary_resolution);
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

    Some(Action::Ambiguous {
        nfa,
        terminals,
        actions,
    })
}

struct ConflictDifferentiator<'a, 'db> {
    db: &'db dyn Db,
    language: Language<'db>,
    lr0_parse_table: &'a Lr0ParseTable<'db>,
    visited: HashSet<ItemIndex>,
    next: HashMap<Terminal<'db>, HashMap<ConflictedAction<'db>, HashMap<Ambiguity<'db>, History>>>,
}

impl<'a, 'db> ConflictDifferentiator<'a, 'db> {
    fn next_terminals(
        db: &'db dyn Db,
        language: Language<'db>,
        lr0_parse_table: &Lr0ParseTable<'db>,
        conflicts: HashMap<ConflictedAction<'db>, HashMap<Ambiguity<'db>, History>>,
    ) -> HashMap<Terminal<'db>, HashMap<ConflictedAction<'db>, HashMap<Ambiguity<'db>, History>>>
    {
        let mut differentiator = ConflictDifferentiator {
            db,
            language,
            lr0_parse_table,
            visited: HashSet::new(),
            next: HashMap::new(),
        };
        for (action, ambiguities) in conflicts {
            differentiator.visited.clear();
            differentiator.extend_ambiguities(action, ambiguities);
        }
        differentiator.next
    }

    #[instrument(skip_all, fields(action = %action.display(self.db)))]
    fn extend_ambiguities(
        &mut self,
        action: ConflictedAction<'db>,
        ambiguities: HashMap<Ambiguity<'db>, History>,
    ) {
        for (ambiguity, history) in ambiguities {
            trace!(ambiguity = %ambiguity.display(self.db), %history, "Investigating ambiguity");
            let (can_be_empty, derivative) = ambiguity.term_string.next(self.db);
            if can_be_empty {
                self.item_lane_heads(
                    &action,
                    &ambiguity.negative_lookahead,
                    &history,
                    &mut HashSet::new(),
                );
            }
            self.add_derivative(derivative, &action, ambiguity.negative_lookahead, history);
        }
    }

    #[instrument(level = "trace", skip_all, fields(location = %history.last().location))]
    fn item_lane_heads(
        &mut self,
        action: &ConflictedAction<'db>,
        negative_lookahead: &[TermString<'db>],
        history: &History,
        mut visited: &mut HashSet<ItemIndex>,
    ) {
        trace!("Computing lane heads");
        let (item, back_refs) = &self.lr0_parse_table[history.last().location];

        let is_lane_head = item.index == 0;
        for &back_ref in back_refs {
            if is_lane_head && !visited.insert(back_ref) {
                continue;
            }
            let mut visited = scopeguard::guard(&mut visited, |visited| {
                if is_lane_head {
                    visited.remove(&back_ref);
                }
            });
            if !self.visited.insert(back_ref) {
                let mut merged = false;
                for actions in self.next.values_mut() {
                    let Some(ambiguities) = actions.get_mut(action) else {
                        continue;
                    };
                    for existing_history in ambiguities.values_mut() {
                        merged |= existing_history.try_merge(back_ref, history, is_lane_head);
                    }
                }
                if merged {
                    continue;
                }
            }
            let mut new_history = history.clone();
            if is_lane_head {
                new_history.prepend_lane_head(back_ref);
            } else {
                new_history.prepend_empty(back_ref);
            }
            if !is_lane_head
                || self.add_lane_head(action, negative_lookahead.to_vec(), new_history.clone())
                    == ControlFlow::Continue(())
            {
                self.item_lane_heads(action, negative_lookahead, &new_history, *visited);
            }
        }
    }

    #[instrument(
        level = "trace",
        skip_all,
        fields(action = %action.display(self.db), history = %history)
    )]
    fn add_lane_head(
        &mut self,
        action: &ConflictedAction<'db>,
        negative_lookahead: Vec<TermString<'db>>,
        history: History,
    ) -> ControlFlow<()> {
        trace!("Walking parse table");
        let item = &self.lr0_parse_table[history.last().location].0;
        let term_string = TermString::new(
            self.db,
            self.language,
            Alternative::new(
                self.db,
                item.alternative.terms(self.db)[item.index + 1..].to_vec(),
                item.alternative.negative_lookahead(self.db),
            ),
        );
        let (can_be_empty, derivative) = term_string.next(self.db);
        self.add_derivative(derivative, action, negative_lookahead, history);
        if can_be_empty {
            ControlFlow::Continue(())
        } else {
            ControlFlow::Break(())
        }
    }
    #[instrument(
        level = "trace",
        skip_all,
        fields(action = %action.display(self.db), history = %history)
    )]
    fn add_derivative(
        &mut self,
        derivative: HashMap<Terminal<'db>, HashSet<TermString<'db>>>,
        action: &ConflictedAction<'db>,
        negative_lookahead: Vec<TermString<'db>>,
        mut history: History,
    ) {
        history.last_mut().terminals_yielded = history
            .last()
            .terminals_yielded
            .iter()
            .map(|i| *i + 1)
            .collect();
        for (terminal, term_strings) in derivative {
            let negative_lookahead: Vec<_> = negative_lookahead
                .iter()
                .flat_map(|terms| terms.next(self.db).1.remove(&terminal))
                .flatten()
                .collect();
            if negative_lookahead
                .iter()
                .any(|term_string| term_string.next(self.db).0)
            {
                trace!("Dropping ambiguity because negative lookahead matched");
                continue;
            }
            let action_ambiguities = self
                .next
                .entry(terminal)
                .or_default()
                .entry(action.clone())
                .or_default();
            for term_string in term_strings {
                action_ambiguities
                    .entry(Ambiguity {
                        location: history.last().location,
                        term_string,
                        negative_lookahead: negative_lookahead.clone(),
                    })
                    .and_modify(|old_history| old_history.merge(history.clone()))
                    .or_insert_with(|| history.clone());
            }
        }
    }
}

fn conflicts<'db>(
    db: &'db dyn Db,
    next_state: &Lr0State<'db>,
    state_id: Lr0StateId,
    language: Language<'db>,
) -> HashMap<ConflictedAction<'db>, HashMap<Ambiguity<'db>, History>> {
    let conflicts: HashMap<_, _> = next_state
        .item_set
        .iter()
        .enumerate()
        .filter_map(|(item_idx, (item, _))| {
            let (conflict, negative_lookahead) = match item.next(db) {
                Some(Term {
                    kind: TermKind::NonTerminal(_),
                    ..
                }) => return None,
                Some(Term {
                    kind: TermKind::Terminal(terminal),
                    ..
                }) => {
                    let next_state = StateId(next_state.actions[&terminal].0);
                    (ConflictedAction::Shift(terminal, next_state), Vec::new())
                }
                None => {
                    let remaining_negative_lookahead: Vec<_> =
                        match item.alternative.negative_lookahead(db) {
                            Some(negative_lookahead) => vec![TermString::new(
                                db,
                                language,
                                Alternative::new(
                                    db,
                                    vec![Term {
                                        kind: TermKind::NonTerminal(negative_lookahead),
                                        silent: false,
                                    }],
                                    None,
                                ),
                            )],
                            None => Vec::new(),
                        };

                    (
                        ConflictedAction::Reduce(item.non_terminal, item.alternative),
                        remaining_negative_lookahead,
                    )
                }
            };
            if negative_lookahead
                .iter()
                .any(|term_string| term_string.next(db).0)
            {
                // If negative lookahead is finished then this action doesn't exist.
                return None;
            }
            let location = ItemIndex {
                state_id,
                item: item_idx,
            };
            let mut ambiguities = HashMap::new();
            ambiguities.insert(
                Ambiguity {
                    location,
                    term_string: TermString::new(
                        db,
                        language,
                        Alternative::new(
                            db,
                            item.alternative.terms(db)[item.index..].to_vec(),
                            item.alternative.negative_lookahead(db),
                        ),
                    ),
                    negative_lookahead,
                },
                History::new(location),
            );
            Some((conflict, ambiguities))
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Ambiguity<'db> {
    location: ItemIndex,
    term_string: TermString<'db>,
    negative_lookahead: Vec<TermString<'db>>,
}

impl<'db> DisplayWithDb for Ambiguity<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        write!(
            f,
            "Ambiguity for {} ({})",
            self.location,
            self.term_string.display(db)
        )
    }
}

#[derive(Debug, Clone)]
struct History {
    /// Note this is in reverse order for easy push
    linear: Vec<HistoryItem>,
    prev: Vec<History>,
}

#[derive(Debug, Clone)]
struct HistoryItem {
    location: ItemIndex,
    terminals_yielded: BTreeSet<u32>,
}

impl History {
    fn new(location: ItemIndex) -> Self {
        let mut terminals_yielded = BTreeSet::new();
        terminals_yielded.insert(0);
        let item = HistoryItem {
            location,
            terminals_yielded,
        };
        Self {
            linear: vec![item],
            prev: vec![],
        }
    }

    fn last(&self) -> &HistoryItem {
        self.linear.last().unwrap()
    }

    fn last_mut(&mut self) -> &mut HistoryItem {
        self.linear.last_mut().unwrap()
    }

    fn prepend_empty(&mut self, location: ItemIndex) {
        self.linear.push(HistoryItem {
            location,
            terminals_yielded: BTreeSet::new(),
        });
    }

    fn prepend_lane_head(&mut self, location: ItemIndex) {
        let mut terminals_yielded = BTreeSet::new();
        terminals_yielded.insert(0);
        self.linear.push(HistoryItem {
            location,
            terminals_yielded,
        });
    }

    fn merge(&mut self, mut other: History) {
        let mut current = self.linear.pop().unwrap();
        let other_current = other.linear.pop().unwrap();
        assert_eq!(current.location, other_current.location);
        current
            .terminals_yielded
            .extend(other_current.terminals_yielded);
        let this = std::mem::replace(
            self,
            History {
                linear: Vec::new(),
                prev: Vec::new(),
            },
        );
        *self = History {
            linear: vec![current],
            prev: vec![this, other],
        }
    }

    fn try_merge(&mut self, location: ItemIndex, other: &History, is_lane_head: bool) -> bool {
        for (i, item) in self
            .linear
            .iter_mut()
            .enumerate()
            .rev()
            .skip(if is_lane_head { 0 } else { 1 })
        {
            match item.terminals_yielded.last() {
                Some(&x) if x > 0 => {
                    return false;
                }
                Some(_) => {}
                None => continue,
            }
            if item.location != location {
                continue;
            }
            let other = other.clone();
            if i == 0 {
                self.prev.push(other);
            } else {
                let mut old = std::mem::replace(
                    self,
                    History {
                        linear: Vec::new(),
                        prev: Vec::new(),
                    },
                );
                let recent = old.linear.split_off(i);
                *self = History {
                    linear: recent,
                    prev: vec![old, other],
                };
            }
            return true;
        }
        for prev in &mut self.prev {
            if prev.try_merge(location, other, false) {
                return true;
            }
        }

        false
    }

    fn loop_lengths(&self, mut action: impl FnMut(u32)) {
        fn loop_lengths(
            loc: ItemIndex,
            mut counts: BTreeSet<u32>,
            linear: &[HistoryItem],
            prev: &[History],
            action: &mut impl FnMut(u32),
        ) {
            for item in linear.iter().rev() {
                if !item.terminals_yielded.is_empty() {
                    let prev_counts = std::mem::take(&mut counts);
                    for &terminals_yielded in &item.terminals_yielded {
                        counts.extend(prev_counts.iter().map(|x| x + terminals_yielded));
                    }
                }
                for &count in &counts {
                    if item.location == loc {
                        action(count);
                    }
                }
            }
            for prev in prev {
                loop_lengths(loc, counts.clone(), &prev.linear, &prev.prev, action);
            }
        }

        // The loop length is from the start of the last time we saw this item to
        // the *start* of this item.
        let loc = self.last().location;
        let mut counts = BTreeSet::new();
        counts.insert(0);
        loop_lengths(
            loc,
            counts,
            &self.linear[..self.linear.len() - 1],
            &self.prev,
            &mut action,
        )
    }
}

impl fmt::Display for History {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.linear.iter().rev().format_with(", ", |item, f| {
                f(&item.location)?;
                if !item.terminals_yielded.is_empty() {
                    f(&format_args!(
                        "x{{{}}}",
                        item.terminals_yielded.iter().format(",")
                    ))?;
                }
                Ok(())
            })
        )?;

        match self.prev.as_slice() {
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

struct StateSplitter<'a, 'db, F> {
    db: &'db dyn Db,
    language: Language<'db>,
    lr0_parse_table: &'a mut Lr0ParseTable<'db>,
    sccs: &'a mut StronglyConnectedComponents,
    invalidate_state: &'a mut F,
    component_paths: HashMap<ComponentId, HashMap<Vec<ComponentId>, usize>>,
    components_splits: HashMap<ComponentId, Vec<ComponentId>>,
    old_to_new_state_map: HashMap<(ComponentId, Lr0StateId), Lr0StateId>,
    new_to_old_state_map: HashMap<Lr0StateId, Lr0StateId>,
}

impl<'a, 'db, F: FnMut(Lr0StateId)> StateSplitter<'a, 'db, F> {
    #[instrument(level = "debug", skip_all)]
    fn split_states(
        db: &'db dyn Db,
        language: Language<'db>,
        lr0_parse_table: &'a mut Lr0ParseTable<'db>,
        sccs: &'a mut StronglyConnectedComponents,
        invalidate_state: &'a mut F,
        state: Lr0StateId,
        next: &HashMap<
            Terminal<'db>,
            HashMap<ConflictedAction<'db>, HashMap<Ambiguity<'db>, History>>,
        >,
    ) -> bool {
        let mut splitter = Self {
            db,
            language,
            lr0_parse_table,
            sccs,
            invalidate_state,
            component_paths: HashMap::new(),
            components_splits: HashMap::new(),
            old_to_new_state_map: HashMap::new(),
            new_to_old_state_map: HashMap::new(),
        };
        let ambiguities: Vec<_> = next
            .iter()
            .flat_map(|(terminal, actions)| actions.iter().map(move |item| (terminal, item)))
            .flat_map(|(terminal, (action, ambiguities))| {
                ambiguities
                    .values()
                    .map(move |history| (history, history.last().location, terminal, action))
            })
            .fold(Vec::new(), |mut acc, (history, loc, terminal, action)| {
                fn recurse<'db>(
                    db: &dyn Db,
                    history: &History,
                    loc: ItemIndex,
                    terminal: &Terminal<'db>,
                    action: &ConflictedAction<'db>,
                    path: &mut VecDeque<Lr0StateId>,
                    acc: &mut Vec<(
                        VecDeque<Lr0StateId>,
                        ItemIndex,
                        Terminal<'db>,
                        ConflictedAction<'db>,
                    )>,
                ) {
                    path.extend(
                        history
                            .linear
                            .iter()
                            .rev()
                            .map(|item| item.location.state_id),
                    );
                    if history.prev.is_empty() {
                        trace!(
                            path = %path.iter().format(","),
                            terminal = %terminal.display(db),
                            action = %action.display(db),
                            "Found ambiguity"
                        );
                        acc.push((path.clone(), loc, terminal.clone(), action.clone()));
                    } else {
                        for prev in &history.prev {
                            recurse(db, prev, loc, terminal, action, path, acc);
                        }
                    }
                    path.pop_back();
                }
                recurse(
                    db,
                    history,
                    loc,
                    terminal,
                    action,
                    &mut VecDeque::new(),
                    &mut acc,
                );
                acc
            });
        let mut splits = Vec::new();
        let component = splitter.sccs.component(state);
        splitter.trace_paths(
            ambiguities,
            component,
            HashMap::new(),
            &mut vec![component],
            &mut splits,
        );
        if splits.len() <= 1 {
            return false;
        }
        let splits = splits
            .into_iter()
            .enumerate()
            .flat_map(|(i, (_, paths))| {
                paths
                    .into_iter()
                    .map(move |mut path| (path.pop().unwrap(), (path, i)))
            })
            .into_group_map();
        for (start, paths) in splits {
            // Paths definitely have at least two components as there must be
            // more than one split and therefore more than one path.
            for (component, paths) in paths
                .into_iter()
                .map(|(mut path, i)| (path.pop().unwrap(), (path, i)))
                .into_group_map()
            {
                splitter.split(start, component, paths);
            }
        }
        true
    }

    fn trace_paths(
        &self,
        mut ambiguities: Vec<(
            VecDeque<Lr0StateId>,
            ItemIndex,
            Terminal<'a>,
            ConflictedAction<'a>,
        )>,
        component: ComponentId,
        mut lookahead: HashMap<Terminal<'a>, HashSet<ConflictedAction<'a>>>,
        path: &mut Vec<ComponentId>,
        splits: &mut Vec<(
            Option<HashMap<Terminal<'a>, HashSet<ConflictedAction<'a>>>>,
            Vec<Vec<ComponentId>>,
        )>,
    ) {
        let mut conflicted_locations: HashMap<ItemIndex, HashSet<ConflictedAction>> =
            HashMap::new();
        ambiguities.retain_mut(|(history, loc, terminal, action)| {
            while let Some(loc) = history.back() {
                if self.sccs.component(*loc) != component {
                    return true;
                }
                history.pop_back();
            }
            lookahead
                .entry(terminal.clone())
                .or_default()
                .insert(action.clone());
            conflicted_locations
                .entry(*loc)
                .or_default()
                .insert(action.clone());
            false
        });
        for (loc, actions) in conflicted_locations {
            if actions.len() > 1 {
                emit(
                    format!(
                        "Conflict at {} between: {}",
                        loc,
                        actions
                            .iter()
                            .format_with(", ", |action, f| f(&action.display(self.db)))
                    ),
                    vec![(Span { start: 0, end: 0 }, None)],
                );
                return;
            }
        }

        if !ambiguities.is_empty() {
            for &next_component in self.sccs.back_refs(component) {
                let ambiguities = ambiguities
                    .iter()
                    .filter(|(history, _, _, _)| {
                        self.sccs.component(*history.back().unwrap()) == next_component
                    })
                    .cloned()
                    .collect();
                path.push(next_component);
                self.trace_paths(ambiguities, next_component, lookahead.clone(), path, splits);
                path.pop();
            }
        } else {
            // First check if there are any conflicts between lookahead tokens
            // that could never be resolved.
            for terminal_a in lookahead.keys() {
                for terminal_b in lookahead.keys() {
                    if terminal_a == terminal_b {
                        continue;
                    }
                    if let Err(diagnostic) = terminals_conflict(
                        self.db,
                        self.language,
                        terminal_a.clone(),
                        terminal_b.clone(),
                    ) {
                        emit_diagnostic(diagnostic);
                        return;
                    }
                }
            }
            // Next check if there are any overlaps between actions that mean
            // we'll have to extend the lookahead.
            if lookahead.values().any(|actions| actions.len() > 1) {
                // This path is ambiguous in itself, hopefully the next
                // lookahead terminal will disambiguate.
                match splits.iter_mut().find(|(info, _)| info.is_none()) {
                    Some((_, paths)) => paths.push(path.clone()),
                    None => splits.push((None, vec![path.clone()])),
                }
            } else {
                // This path is unambiguous, so lets try and merge it with an
                // existing split if possible.
                let existing_split = splits.iter_mut().find(|(split_lookahead, _)| {
                    let Some(split_lookahead) = split_lookahead else {
                        return false;
                    };
                    // Check that none of the terminals conflict and that
                    // they don't introduce any action conflicts.
                    for (terminal, action) in &lookahead {
                        if let Some(split_action) = split_lookahead.get(terminal) {
                            if action != split_action {
                                return false;
                            }
                        } else {
                            for split_terminal in split_lookahead.keys() {
                                if terminals_conflict(
                                    self.db,
                                    self.language,
                                    terminal.clone(),
                                    split_terminal.clone(),
                                )
                                .is_err()
                                {
                                    return false;
                                }
                            }
                        }
                    }
                    true
                });
                match existing_split {
                    Some((_, split_paths)) => split_paths.push(path.clone()),
                    None => splits.push((Some(lookahead.clone()), vec![path.clone()])),
                }
            }
        }
    }

    fn split(
        &mut self,
        prev_component: ComponentId,
        component: ComponentId,
        paths: Vec<(Vec<ComponentId>, usize)>,
    ) {
        let new_component = self
            .components_splits
            .get(&component)
            .into_iter()
            .flatten()
            .copied()
            .find(|component| {
                let existing_paths = &self.component_paths[component];
                paths.iter().all(|(path, split)| {
                    let existing_split = existing_paths.get(path);
                    existing_split.is_none() || existing_split == Some(split)
                })
            })
            .unwrap_or_else(|| self.split_component(component));
        self.patch_component(
            prev_component,
            *self.components_splits[&component]
                .iter()
                .find(|c| self.sccs.refs(prev_component).contains(c))
                .unwrap(),
            new_component,
        );
        self.component_paths
            .entry(new_component)
            .or_default()
            .extend(paths.iter().cloned());
        for (next_component, paths) in paths
            .into_iter()
            .filter_map(|(mut path, split)| path.pop().map(|component| (component, (path, split))))
            .into_group_map()
        {
            self.split(new_component, next_component, paths);
        }
    }

    fn split_component(&mut self, component: ComponentId) -> ComponentId {
        if !self
            .component_paths
            .get(&component)
            .is_some_and(|set| !set.is_empty())
        {
            // If there are no paths associated with the component then we can
            // just use it directly.
            for &state in &self.sccs.components[component.0].states {
                self.sccs.component_map.insert(state, component);
                self.old_to_new_state_map.insert((component, state), state);
                self.new_to_old_state_map.insert(state, state);
            }
            self.components_splits.insert(component, vec![component]);
            return component;
        }

        let new_component_id = ComponentId(self.sccs.components.len());
        let mut states = HashSet::new();
        for &old_state in &self.sccs.components[component.0].states {
            let new_state_id = Lr0StateId(self.lr0_parse_table.states.len());
            let new_state = self.lr0_parse_table[old_state].clone();

            for next_state_id in Iterator::chain(
                new_state.actions.values().copied(),
                new_state.goto.values().copied(),
            ) {
                if self.sccs.components[component.0]
                    .states
                    .contains(&next_state_id)
                {
                    continue;
                }
                for (_, back_refs) in &mut self.lr0_parse_table[next_state_id].item_set {
                    let mut to_insert = Vec::new();
                    for back_ref in &*back_refs {
                        if back_ref.state_id == old_state {
                            to_insert.push(ItemIndex {
                                state_id: new_state_id,
                                item: back_ref.item,
                            });
                        }
                    }
                    back_refs.extend(to_insert);
                }
            }

            self.lr0_parse_table.states.push(new_state);
            (self.invalidate_state)(new_state_id);
            self.sccs
                .component_map
                .insert(new_state_id, new_component_id);
            states.insert(new_state_id);
            self.old_to_new_state_map
                .insert((new_component_id, old_state), new_state_id);
            self.new_to_old_state_map.insert(new_state_id, old_state);
        }
        for &state in &states {
            let state = &mut self.lr0_parse_table[state];
            for (_, back_refs) in &mut state.item_set {
                let old_back_refs = std::mem::take(back_refs);
                for mut back_ref in old_back_refs {
                    if let Some(new_state) = self
                        .old_to_new_state_map
                        .get(&(new_component_id, back_ref.state_id))
                    {
                        back_ref.state_id = *new_state;
                        back_refs.insert(back_ref);
                    }
                }
            }
            for next_state in Iterator::chain(state.actions.values_mut(), state.goto.values_mut()) {
                if let Some(new_state) = self
                    .old_to_new_state_map
                    .get(&(new_component_id, *next_state))
                {
                    *next_state = *new_state;
                }
            }
        }
        let new_component = Component {
            states,
            forward_refs: self.sccs.refs(component).clone(),
            backward_refs: HashSet::new(),
        };
        for next_component in &new_component.forward_refs {
            self.sccs.components[next_component.0]
                .backward_refs
                .insert(new_component_id);
        }
        self.sccs.components.push(new_component);
        self.components_splits
            .entry(component)
            .or_default()
            .push(new_component_id);
        new_component_id
    }

    fn patch_component(
        &mut self,
        component_id: ComponentId,
        old_dest_id: ComponentId,
        new_dest_id: ComponentId,
    ) {
        if old_dest_id == new_dest_id {
            return;
        }

        fn get_3_components(
            components: &mut [Component],
            a: ComponentId,
            b: ComponentId,
            c: ComponentId,
        ) -> (&mut Component, &mut Component, &mut Component) {
            assert_ne!(a, b);
            assert_ne!(b, c);
            assert_ne!(a, c);
            assert!((0..components.len()).contains(&a.0));
            assert!((0..components.len()).contains(&b.0));
            assert!((0..components.len()).contains(&c.0));
            let components = components.as_mut_ptr();
            unsafe {
                (
                    &mut *components.add(a.0),
                    &mut *components.add(b.0),
                    &mut *components.add(c.0),
                )
            }
        }
        let (component, old_dest, new_dest) = get_3_components(
            &mut self.sccs.components,
            component_id,
            old_dest_id,
            new_dest_id,
        );

        old_dest.backward_refs.remove(&component_id);
        new_dest.backward_refs.insert(component_id);
        component.forward_refs.remove(&old_dest_id);
        component.forward_refs.insert(new_dest_id);

        for &state_id in &component.states {
            (self.invalidate_state)(state_id);
            let states = self.lr0_parse_table.states.as_mut_slice();
            assert!(state_id.0 < states.len());
            let state = unsafe { &mut *states.as_mut_ptr().add(state_id.0) };
            for dest_state in
                std::iter::Iterator::chain(state.actions.values_mut(), state.goto.values_mut())
                    .filter(|id| old_dest.states.contains(id))
            {
                let old_dest_state_id = *dest_state;
                let new_dest_state_id = self.old_to_new_state_map[&(
                    new_dest_id,
                    self.new_to_old_state_map
                        .get(dest_state)
                        .copied()
                        .unwrap_or(*dest_state),
                )];
                *dest_state = new_dest_state_id;

                assert_ne!(state_id, old_dest_state_id);
                assert_ne!(state_id, new_dest_state_id);
                assert_ne!(old_dest_state_id, new_dest_state_id);
                assert!(old_dest_state_id.0 < states.len());
                assert!(new_dest_state_id.0 < states.len());
                let old_dest_state = unsafe { &mut *states.as_mut_ptr().add(old_dest_state_id.0) };
                let new_dest_state = unsafe { &mut *states.as_mut_ptr().add(new_dest_state_id.0) };
                for ((_, old_back_refs), (_, new_back_refs)) in std::iter::zip(
                    old_dest_state.item_set.iter_mut(),
                    new_dest_state.item_set.iter_mut(),
                ) {
                    old_back_refs.retain(|old_back_ref| {
                        if old_back_ref.state_id == state_id {
                            new_back_refs.insert(ItemIndex {
                                state_id,
                                item: old_back_ref.item,
                            });
                            false
                        } else {
                            true
                        }
                    });
                }
            }
        }
    }
}
