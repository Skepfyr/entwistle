use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt,
    ops::Index,
    sync::Arc,
};

use im::OrdSet;
use tracing::{debug, instrument, trace};

use crate::{
    lower::{Lower, NonTerminal, NonTerminalData, Term, Terminal},
    util::DbDisplay,
};

#[salsa::query_group(ParseTableStorage)]
pub trait ParseTable: Lower {
    #[salsa::interned]
    fn intern_item_set(&self, data: ItemSetData) -> ItemSet;
    fn first_set(&self, non_terminal: NonTerminal) -> (bool, OrdSet<Terminal>);
    fn lr0_parse_table(&self, start_symbol: NonTerminal) -> Lr0ParseTable;
    #[salsa::cycle(resolve_lane_cycle)]
    fn item_lane_heads(&self, start_symbol: NonTerminal, item: ItemIndex) -> BTreeSet<ItemIndex>;
    fn item_set_lane_heads(
        &self,
        start_symbol: NonTerminal,
        cycle: Arc<BTreeSet<ItemIndex>>,
    ) -> BTreeSet<ItemIndex>;
    fn parse_table(&self, start_symbol: NonTerminal) -> LrkParseTable;
    fn lane_table(&self, start_symbol: NonTerminal) -> Arc<LaneTable>;
    fn normal_production(&self, non_terminal: NormalNonTerminal) -> OrdSet<Arc<[NormalTerm]>>;
    fn left_recursive(&self, non_terminal: NonTerminal) -> bool;
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LrkParseTable {
    states: Arc<[State]>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct State {
    action: Action,
    goto: BTreeMap<NonTerminal, usize>,
    accepting: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Action {
    Ambiguous(Arc<[(Terminal, Action)]>),
    Shift(Terminal, StateId),
    Reduce(NonTerminal, Arc<[Term]>),
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

    fn is_nucleus(&self) -> bool {
        self.index != 0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct StateId(usize);

impl fmt::Display for StateId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ItemIndex {
    state: StateId,
    item: usize,
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
    pub start_state: StateId,
    pub states: Arc<[Lr0State]>,
}

impl<Db: ParseTable> DbDisplay<Db> for Lr0ParseTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result {
        writeln!(f, "Start state: {}", self.start_state)?;
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

impl Index<StateId> for Lr0ParseTable {
    type Output = Lr0State;

    fn index(&self, index: StateId) -> &Self::Output {
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
    pub actions: HashMap<Terminal, StateId>,
    pub goto: HashMap<NonTerminal, StateId>,
}

impl Lr0State {
    fn is_ambiguous(&self) -> bool {
        let reductions = self
            .item_set
            .iter()
            .filter(|(item, _)| item.next().is_none())
            .count();
        reductions > 1 || (reductions > 0 && !self.actions.is_empty())
    }
}

intern_key!(ItemSet);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ItemSetData {
    items: Vec<(Item, BTreeSet<ItemIndex>)>,
}

pub fn lr0_parse_table(db: &dyn ParseTable, start_symbol: NonTerminal) -> Lr0ParseTable {
    let mut states: Vec<Lr0State> = Vec::new();
    let mut state_lookup: HashMap<BTreeSet<Item>, StateId> = HashMap::new();

    let goal = db.intern_non_terminal(NonTerminalData::Goal {
        non_terminal: start_symbol,
    });

    let mut root_item_set = BTreeSet::new();
    for production in db.production(goal) {
        // There should only be one but doesn't hurt to add them "all"
        root_item_set.insert(Item {
            non_terminal: goal,
            production,
            index: 0,
        });
    }
    add_state(db, &mut states, &root_item_set);

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
                        state: StateId(state_id),
                        item: id,
                    });
            }
            let new_item_set = new_state.iter().map(|(item, _)| item.clone()).collect();
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
        start_state: StateId(0),
        states: states.into(),
    }
}

fn add_state(db: &dyn ParseTable, states: &mut Vec<Lr0State>, state: &BTreeSet<Item>) -> StateId {
    let new_id = StateId(states.len());
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
    state_id: StateId,
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

pub fn item_lane_heads(
    db: &dyn ParseTable,
    start_symbol: NonTerminal,
    item: ItemIndex,
) -> BTreeSet<ItemIndex> {
    let mut set = BTreeSet::new();
    set.insert(item);
    lane_heads(db, start_symbol, Arc::new(set))
}

fn resolve_lane_cycle(
    db: &dyn ParseTable,
    _cycle: &[String],
    start_symbol: &NonTerminal,
    root_item_id: &ItemIndex,
) -> BTreeSet<ItemIndex> {
    let parse_table = db.lr0_parse_table(*start_symbol);
    let mut visited = HashSet::new();
    let mut cycle = BTreeSet::new();

    visited.insert(*root_item_id);
    cycle.insert(*root_item_id);
    find_cycle(&parse_table, &mut visited, &mut cycle, *root_item_id);

    db.item_set_lane_heads(*start_symbol, Arc::new(cycle))
}

fn find_cycle(
    parse_table: &Lr0ParseTable,
    visited: &mut HashSet<ItemIndex>,
    cycle: &mut BTreeSet<ItemIndex>,
    item: ItemIndex,
) {
    let (_, back_refs) = &parse_table[item];

    let in_cycle = back_refs.iter().any(|&back_ref| {
        if visited.insert(back_ref) {
            find_cycle(parse_table, visited, cycle, back_ref);
        }

        cycle.contains(&back_ref)
    });

    if in_cycle {
        cycle.insert(item);
    }
}

fn item_set_lane_heads(
    db: &dyn ParseTable,
    start_symbol: NonTerminal,
    cycle: Arc<BTreeSet<ItemIndex>>,
) -> BTreeSet<ItemIndex> {
    lane_heads(db, start_symbol, cycle)
}

fn lane_heads(
    db: &dyn ParseTable,
    start_symbol: NonTerminal,
    cycle: Arc<BTreeSet<ItemIndex>>,
) -> BTreeSet<ItemIndex> {
    let parse_table = db.lr0_parse_table(start_symbol);

    cycle.iter().fold(BTreeSet::new(), |mut context, &item_id| {
        let (item, back_refs) = &parse_table[item_id];

        if item.is_nucleus() {
            back_refs
                .difference(&cycle)
                .fold(context, |mut context, &prev_item| {
                    context.extend(&db.item_lane_heads(start_symbol, prev_item));
                    context
                })
        } else {
            context.extend(back_refs.difference(&cycle));
            context
        }
    })
}

fn parse_table(db: &dyn ParseTable, start_symbol: NonTerminal) -> LrkParseTable {
    todo!()
    // let lr0_parse_table = db.lr0_parse_table(start_symbol);
    // let lane_table = db.lane_table(start_symbol);
    // let sorted = sorted_condensation(&lr0_parse_table);
    // let mut states = Vec::with_capacity(lr0_parse_table.states.len());
    // let mut state_map: HashMap<StateId, Vec<usize>> =
    //     HashMap::with_capacity(lr0_parse_table.states.len());
    // pub enum TempAction {
    //     Ambiguous(Arc<[(Terminal, Action)]>),
    //     Shift(Terminal, (StateId, usize)),
    //     Reduce(NonTerminal, Arc<[Term]>),
    // }
    // struct TempState {
    //     action: TempAction,
    //     goto: BTreeMap<NonTerminal, (StateId, usize)>,
    //     accepting: bool,
    // }

    // for states in sorted.into_iter().rev() {
    //     let state_to_add = &lr0_parse_table[state_id_to_add];
    //     let shifts = &state_to_add.actions;
    //     let reductions: Vec<_> = state_to_add
    //         .item_set
    //         .iter()
    //         .map(|(item, _)| item)
    //         .filter(|item| item.next().is_none())
    //         .collect();
    //     let action = match (shifts.len(), reductions.len()) {
    //         (0, 0) => panic!("All states must have an action?"),
    //         (1, 0) => {
    //             let (terminal, state_id) = shifts.iter().next().unwrap();
    //             TempAction::Shift(terminal, (state_id, ))
    //         }
    //         (_, 0) => {}
    //         (0, 1) => {}
    //         (_, _) => {}
    //     };

    //     states.push(TempState {
    //         action,
    //         goto,
    //         accepting: state_to_add.accepting,
    //     });
    // }

    // LrkParseTable {
    //     states: states
    //         .into_iter()
    //         .map(|state: TempState| State {
    //             action: state.action,
    //             goto: state
    //                 .goto
    //                 .into_iter()
    //                 .map(|(nt, (id, idx))| (nt, state_map[&id][idx]))
    //                 .collect(),
    //             accepting: state.accepting,
    //         })
    //         .collect(),
    // }
}

fn sorted_condensation(parse_table: &Lr0ParseTable) -> Vec<Vec<usize>> {
    todo!()
}

type LaneTable = BTreeMap<StateId, BTreeMap<(StateId, ConflictedAction), BTreeSet<Vec<Terminal>>>>;

impl<Db: ParseTable> DbDisplay<Db> for LaneTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result {
        for (source_state, conflicts) in self {
            writeln!(f, "Source state {}:", source_state)?;
            for ((state, conflict), disambiguators) in conflicts {
                write!(f, "  State {}: {}", state, conflict.display(db))?;
                for disambiguator in disambiguators {
                    write!(f, "   ")?;
                    for &terminal in disambiguator {
                        write!(f, " {}", terminal.display(db))?;
                    }
                    writeln!(f)?;
                }
            }
        }
        Ok(())
    }
}

fn lane_table(db: &dyn ParseTable, start_symbol: NonTerminal) -> Arc<LaneTable> {
    let parse_table = db.lr0_parse_table(start_symbol);
    let mut disambiguator = Disambiguator::new(db, start_symbol);
    for (state_id, state) in parse_table.states.iter().enumerate() {
        let state_id = StateId(state_id);
        if state.is_ambiguous() {
            let ambiguities = state
                .item_set
                .iter()
                .enumerate()
                .flat_map(|(i, (item, _))| {
                    let action = match item.next() {
                        Some(Term::Terminal(terminal)) => ConflictedAction::Shift(terminal),
                        Some(Term::NonTerminal(_)) => return None, // The goto table can't cause conflicts
                        None => {
                            ConflictedAction::Reduce(item.non_terminal, item.production.clone())
                        }
                    };
                    let ambiguity = Ambiguity {
                        location: ItemIndex {
                            state: state_id,
                            item: i,
                        },
                        history: Some(HashSet::new()),
                        term_string: Arc::new(TermString {
                            non_terminal: None,
                            // Can convert directly from a non-normalised to normalised production
                            // because this "non-terminal" doesn't exist in the grammar and so can't
                            // be left-recursive. The logic breaks slightly if item.index == 0, but
                            // at worst it will cause an extra loop to happen so is fine.
                            terms: item
                                .production
                                .iter()
                                .map(|&term| term.into())
                                .collect::<Vec<_>>()
                                .into(),
                            next_term: item.index,
                            parent: None,
                            contains_loop: false,
                        }),
                    };
                    Some((action, vec![ambiguity]))
                })
                .collect();
            disambiguator.disambiguate_prefix(state_id, Vec::new(), ambiguities);
        }
    }
    Arc::new(disambiguator.lane_table)
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConflictedAction {
    Shift(Terminal),
    Reduce(NonTerminal, Arc<[Term]>),
}

impl<Db: ParseTable> DbDisplay<Db> for ConflictedAction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result {
        match self {
            ConflictedAction::Shift(terminal) => {
                writeln!(f, "Shift({})", terminal.display(db))?;
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

#[derive(Debug)]
struct Ambiguity {
    location: ItemIndex,
    history: Option<HashSet<ItemIndex>>,
    term_string: Arc<TermString>,
}

impl Ambiguity {
    fn contains_loop(&self) -> bool {
        self.history.is_none() || self.term_string.contains_loop
    }
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

struct Disambiguator<'a> {
    db: &'a dyn ParseTable,
    start_symbol: NonTerminal,
    lane_table: LaneTable,
}

impl<'a> Disambiguator<'a> {
    fn new(db: &'a dyn ParseTable, start_symbol: NonTerminal) -> Self {
        Self {
            db,
            start_symbol,
            lane_table: LaneTable::new(),
        }
    }

    #[instrument(skip(self, ambiguities))]
    fn disambiguate_prefix(
        &mut self,
        state: StateId,
        prefix: Vec<Terminal>,
        ambiguities: HashMap<ConflictedAction, Vec<Ambiguity>>,
    ) {
        debug!(?ambiguities, len = ambiguities.len());
        assert!(!ambiguities.is_empty());
        if ambiguities.len() == 1 {
            let (action, ambiguities) = ambiguities.into_iter().next().unwrap();
            for ambiguity in ambiguities {
                self.lane_table
                    .entry(ambiguity.location.state)
                    .or_default()
                    .entry((state, action.clone()))
                    .or_default()
                    .insert(prefix.clone());
            }
            return;
        }
        let parse_table = self.db.lr0_parse_table(self.start_symbol);
        let mut next = HashMap::<Terminal, HashMap<ConflictedAction, Vec<Ambiguity>>>::new();

        for (action, mut ambiguities) in ambiguities {
            let mut visited = HashSet::with_capacity(ambiguities.len());
            while let Some(Ambiguity {
                location,
                history,
                mut term_string,
            }) = ambiguities.pop()
            {
                trace!(?location, ?history, ?term_string, "Investigating ambiguity");
                if let Some(term) = term_string.terms.get(term_string.next_term).cloned() {
                    Arc::make_mut(&mut term_string).next_term += 1;
                    match term {
                        NormalTerm::Terminal(terminal) => {
                            trace!(?terminal, "Found terminal");
                            next.entry(terminal)
                                .or_default()
                                .entry(action.clone())
                                .or_default()
                                .push(Ambiguity {
                                    location,
                                    history: history.clone(),
                                    term_string,
                                });
                        }
                        NormalTerm::NonTerminal(non_terminal) => {
                            trace!(?non_terminal, "Walking down into non-terminal");
                            ambiguities.extend(
                                self.db
                                    .normal_production(non_terminal)
                                    .into_iter()
                                    .map(|terms| Ambiguity {
                                        location,
                                        history: history.clone(),
                                        term_string: Arc::new(TermString {
                                            non_terminal: Some(non_terminal),
                                            terms,
                                            next_term: 0,
                                            parent: Some(term_string.clone()),
                                            contains_loop: term_string.contains_loop
                                                || term_string
                                                    .self_and_parents()
                                                    .any(|p| p.non_terminal == Some(non_terminal)),
                                        }),
                                    }),
                            )
                        }
                    }
                    continue;
                } else if let Some(parent) = &term_string.parent {
                    trace!("Walking up to parent");
                    ambiguities.push(Ambiguity {
                        location,
                        history,
                        term_string: parent.clone(),
                    });
                    continue;
                }
                // term_string is empty, so we must now walk the parse table.
                ambiguities.extend(
                    item_lane_heads(self.db, self.start_symbol, location)
                        .into_iter()
                        .filter(|&location| visited.insert(location))
                        .map(|location| {
                            trace!(?location, "Walking parse table");
                            let item = &parse_table[location].0;
                            let history = history.clone().and_then(|mut history| {
                                if history.insert(location) {
                                    Some(history)
                                } else {
                                    None
                                }
                            });

                            Ambiguity {
                                location,
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
                        }),
                );
            }
        }

        for (terminal, ambiguities) in next {
            let all_looping = ambiguities
                .iter()
                .flat_map(|(_, ambiguities)| ambiguities)
                .all(|ambiguity| ambiguity.contains_loop());
            if all_looping {
                panic!("Ambiguous!");
            }
            let mut new_prefix = prefix.clone();
            new_prefix.push(terminal);
            self.disambiguate_prefix(state, new_prefix, ambiguities);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NormalNonTerminal {
    Original(NonTerminal),
    Minus(NonTerminal, Term),
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
