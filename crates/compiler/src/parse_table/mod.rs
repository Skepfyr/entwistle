use std::{
    collections::{hash_map::Entry, BTreeSet, HashMap, HashSet},
    fmt::{self, Write as _},
    hash::Hash,
    ops::Index,
    sync::Arc,
    vec,
};

use indenter::indented;
use regex_automata::{
    nfa::thompson::{State as NfaState, NFA},
    PatternID,
};
use tracing::{debug, debug_span, trace};

use crate::{
    language::Ident,
    lower::{Alternative, Grammar, NonTerminal, Term, TermKind, Terminal},
};

use self::term_string::TermString;

mod term_string;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LrkParseTable {
    pub start_states: HashMap<Ident, StateId>,
    pub states: Vec<State>,
}

impl fmt::Display for LrkParseTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Start states:")?;
        for (ident, state) in &self.start_states {
            writeln!(f, "  {ident} => {state}")?;
        }
        for (i, state) in self.states.iter().enumerate() {
            writeln!(f, "State {i}:")?;
            writeln!(f, "  Actions:")?;
            write!(indented(f).with_str("    "), "{}", state.action)?;
            writeln!(f, "  Goto:")?;
            for (nt, state) in &state.goto {
                writeln!(f, "    {nt} -> {state}")?;
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
        regexes: Vec<String>,
        actions: Vec<Action>,
        eoi: HashMap<Ident, Action>,
    },
    Shift(Terminal, StateId),
    Reduce(NonTerminal, Alternative),
}

impl fmt::Display for Action {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn display(
            action: &Action,
            f: &mut fmt::Formatter<'_>,
            lookahead: &mut Vec<String>,
        ) -> fmt::Result {
            match action {
                Action::Ambiguous {
                    nfa: _,
                    regexes,
                    actions,
                    eoi,
                } => {
                    for (terminal, action) in regexes.iter().zip(actions) {
                        lookahead.push(terminal.clone());
                        display(action, f, lookahead)?;
                        lookahead.pop();
                    }
                    for (ident, action) in eoi {
                        lookahead.push(format!("EOI({})", ident));
                        display(action, f, lookahead)?;
                        lookahead.pop();
                    }
                    Ok(())
                }
                Action::Shift(terminal, state) => {
                    for terminal in lookahead {
                        write!(f, "{terminal} ")?;
                    }
                    writeln!(f, ": Shift({terminal}) -> {state}")
                }
                Action::Reduce(non_terminal, alternative) => {
                    for terminal in lookahead {
                        write!(f, "{terminal} ")?;
                    }
                    writeln!(f, ": Reduce({non_terminal} -> {alternative})")
                }
            }
        }
        display(self, f, &mut Vec::new())
    }
}

impl PartialEq for Action {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Ambiguous {
                    nfa: _,
                    regexes: l_regexes,
                    actions: l_actions,
                    eoi: l_eoi,
                },
                Self::Ambiguous {
                    nfa: _,
                    regexes: r_regexes,
                    actions: r_actions,
                    eoi: r_eoi,
                },
            ) => l_regexes == r_regexes && l_actions == r_actions && l_eoi == r_eoi,
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

    fn next(&self) -> Option<Term> {
        self.alternative.terms.get(self.index).cloned()
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

pub fn first_set(grammar: &Grammar, non_terminal: &NonTerminal) -> (bool, HashSet<Terminal>) {
    grammar.productions[non_terminal]
        .alternatives
        .iter()
        .map(|alternative| alternative.terms.get(0))
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
                }) if nt != non_terminal => {
                    let other = first_set(grammar, nt);
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lr0ParseTable {
    pub start_states: HashMap<Ident, Lr0StateId>,
    pub states: Vec<Lr0State>,
}

impl fmt::Display for Lr0ParseTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Start states:")?;
        for (ident, state) in &self.start_states {
            writeln!(f, "  {ident} => {state}")?;
        }
        for (i, state) in self.states.iter().enumerate() {
            writeln!(f, "State {i}:")?;
            writeln!(indented(f).with_str("  "), "{state}")?;
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lr0State {
    pub item_set: Vec<(Item, BTreeSet<ItemIndex>)>,
    pub actions: HashMap<Terminal, Lr0StateId>,
    pub goto: HashMap<NonTerminal, Lr0StateId>,
}

impl fmt::Display for Lr0State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Items:")?;
        for (item, _backlinks) in &self.item_set {
            write!(f, "    {} ->", item.non_terminal)?;
            for term in &item.alternative.terms[..item.index] {
                write!(f, " {term}")?;
            }
            write!(f, " .")?;
            for term in &item.alternative.terms[item.index..] {
                write!(f, " {term}")?;
            }
            if let Some(lookahead) = &item.alternative.negative_lookahead {
                write!(f, "(!>>{})", lookahead)?;
            }
            writeln!(f)?;
        }
        writeln!(f, "Actions:")?;
        for (t, state) in &self.actions {
            writeln!(f, "  {t} -> {state}")?;
        }
        for (nt, state) in &self.goto {
            writeln!(f, "  {nt} -> {state}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ItemSet {
    items: Vec<(Item, BTreeSet<ItemIndex>)>,
}

pub fn lr0_parse_table(grammar: &Grammar) -> Lr0ParseTable {
    let mut states: Vec<Lr0State> = Vec::new();
    let mut state_lookup: HashMap<BTreeSet<Item>, Lr0StateId> = HashMap::new();

    let mut start_states = HashMap::new();
    for (goal, production) in &grammar.productions {
        let ident = match goal {
            NonTerminal::Goal { ident } => ident.clone(),
            _ => continue,
        };

        let mut root_item_set = BTreeSet::new();
        for alternative in &production.alternatives {
            // There should only be one but doesn't hurt to add them "all"
            root_item_set.insert(Item::new(goal.clone(), alternative.clone()));
        }
        let new_state = add_state(grammar, &mut states, &root_item_set);
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
                if item.next().as_ref() != Some(&term) {
                    continue;
                }
                new_state
                    .entry(Item {
                        non_terminal: item.non_terminal.clone(),
                        alternative: item.alternative.clone(),
                        index: item.index + 1,
                    })
                    .or_default()
                    .insert(ItemIndex {
                        state_id: Lr0StateId(state_id),
                        item: id,
                    });
            }
            let new_item_set = new_state.keys().cloned().collect();
            let next_state_id = *state_lookup
                .entry(new_item_set)
                .or_insert_with_key(|new_item_set| add_state(grammar, &mut states, new_item_set));
            let next_state = &mut states[next_state_id.0];
            for (item, back_refs) in &mut next_state.item_set {
                if let Some(new_back_refs) = new_state.get(item) {
                    back_refs.extend(new_back_refs.iter().copied());
                }
            }
            match term.kind {
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

    Lr0ParseTable {
        start_states,
        states,
    }
}

fn add_state(grammar: &Grammar, states: &mut Vec<Lr0State>, state: &BTreeSet<Item>) -> Lr0StateId {
    let new_id = Lr0StateId(states.len());
    states.push(Lr0State {
        item_set: closure(grammar, state, new_id),
        actions: HashMap::new(),
        goto: HashMap::new(),
    });
    new_id
}

fn closure(
    grammar: &Grammar,
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
            Some(Term {
                kind: TermKind::NonTerminal(nt),
                ..
            }) => nt,
            _ => continue,
        };

        let start = *added
            .entry(non_terminal.clone())
            .or_insert_with_key(|non_terminal| {
                let start = state.len();
                state.extend(
                    grammar.productions[non_terminal]
                        .alternatives
                        .iter()
                        .map(|p| (Item::new(non_terminal.clone(), p.clone()), BTreeSet::new())),
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

pub fn parse_table(grammar: &Grammar) -> LrkParseTable {
    let lr0_parse_table = lr0_parse_table(grammar);
    debug!(%lr0_parse_table, "Generated LR(0) parse table");
    LrkParseTableBuilder {
        grammar,
        lr0_parse_table,
    }
    .build()
}

struct LrkParseTableBuilder<'a> {
    grammar: &'a Grammar,
    lr0_parse_table: Lr0ParseTable,
}

impl<'a> LrkParseTableBuilder<'a> {
    fn build(mut self) -> LrkParseTable {
        let mut states = Vec::new();

        let mut invalidated = Vec::new();
        let mut lr0_state_id = 0;
        while lr0_state_id < self.lr0_parse_table.states.len() {
            let next_state = &self.lr0_parse_table[Lr0StateId(lr0_state_id)];
            let conflicts = conflicts(next_state, lr0_state_id, self.grammar);
            let goto = next_state
                .goto
                .iter()
                .map(|(nt, id)| (nt.clone(), StateId(id.0)))
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
                let span = debug_span!("make_action", state = lr0_state_id);
                let _enter = span.enter();
                debug!("Making top-level action");
                let make_action =
                    self.make_action(visited.clone(), conflicts.clone(), &mut invalidate_state);
                if let Some(action) = make_action {
                    break action;
                }
            };
            states.push(State { action, goto });
            lr0_state_id += 1
        }
        while let Some(lr0_state_id) = invalidated.pop() {
            let next_state = &self.lr0_parse_table[Lr0StateId(lr0_state_id)];
            let conflicts = conflicts(next_state, lr0_state_id, self.grammar);
            let goto = next_state
                .goto
                .iter()
                .map(|(nt, id)| (nt.clone(), StateId(id.0)))
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
                let span = debug_span!("make_action", state = lr0_state_id);
                let _enter = span.enter();
                debug!("Making top-level action");
                let make_action =
                    self.make_action(visited.clone(), conflicts.clone(), &mut invalidate_state);
                if let Some(action) = make_action {
                    break action;
                }
            };
            states[lr0_state_id] = State { action, goto };
        }
        LrkParseTable {
            start_states: self
                .lr0_parse_table
                .start_states
                .into_iter()
                .map(|(k, v)| (k, StateId(v.0)))
                .collect(),
            states,
        }
    }

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
            let span = debug_span!("extend_ambiguities", action = %action);
            let _enter = span.enter();
            let mut lane_members = HashMap::new();
            while let Some(Ambiguity {
                location,
                transition,
                history,
                term_string,
            }) = ambiguities.pop()
            {
                trace!(%location, %history, %term_string, "Investigating ambiguity");
                for (terminal, term_string) in term_string.next(self.grammar) {
                    match terminal {
                        Some(terminal) => {
                            let new_action = action.with_lookahead(self.grammar, terminal.clone());
                            if new_action.contains_finished_lookahead(self.grammar) {
                                trace!("Dropping ambiguity because negative lookahead matched");
                                continue;
                            }
                            let mut history = history.clone();
                            history.0.push((location, term_string.with_no_parent()));
                            next.entry(terminal)
                                .or_default()
                                .entry(new_action)
                                .or_default()
                                .push(Ambiguity {
                                    location,
                                    transition: transition.clone(),
                                    history,
                                    term_string,
                                });
                        }
                        None => {
                            // term_string is empty, so we must now walk the parse table.
                            let mut lane_heads = HashSet::new();
                            potential_ambiguity |= self.item_lane_heads(
                                action.clone(),
                                location,
                                transition.clone(),
                                &mut split_info,
                                &mut lane_members,
                                &mut lane_heads,
                            );
                            ambiguities.extend(lane_heads.into_iter().map(
                                |(location, transition)| {
                                    trace!(%location, "Walking parse table");
                                    let item = &self.lr0_parse_table[location].0;
                                    Ambiguity {
                                        location,
                                        transition,
                                        history: history.clone(),
                                        term_string: TermString::new(
                                            item.alternative
                                                .terms
                                                .iter()
                                                .map(|term| term.kind.clone().into())
                                                .collect::<Vec<_>>(),
                                            item.index + 1,
                                        ),
                                    }
                                },
                            ));
                        }
                    }
                }
            }
            visited.extend(lane_members.into_keys().map(|idx| idx.state_id));
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
                    let next_state = match &next.kind {
                        TermKind::Terminal(t) => self.lr0_parse_table[state].actions[t],
                        TermKind::NonTerminal(nt) => self.lr0_parse_table[state].goto[nt],
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
                                        .filter(|item_idx| item_idx.state_id == state)
                                        .map(|item_idx| ItemIndex {
                                            state_id: new_state_id,
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
            println!("{}", self.lr0_parse_table);
            return None;
        }

        if potential_ambiguity {
            panic!("Ambiguity!");
        }

        let mut regexes = Vec::with_capacity(next.len());
        let mut actions = Vec::with_capacity(next.len());
        let mut eoi = HashMap::new();
        for (terminal, conflicts) in next {
            let loops = conflicts
                .values()
                .map(|v| {
                    v.iter()
                        .flat_map(|ambiguity| {
                            let mut history = ambiguity.history.0.iter().rev();
                            let first = history.next().unwrap();
                            history
                                .enumerate()
                                .filter(move |&(_, entry)| entry == first)
                                .map(|(i, _)| i)
                        })
                        .collect::<HashSet<_>>()
                })
                .collect::<Vec<_>>();
            let contains_common_loops = loops
                .iter()
                .enumerate()
                .any(|(i, set1)| loops[i + 1..].iter().any(|set2| !set1.is_disjoint(set2)));
            if contains_common_loops {
                panic!("Ambiguity!");
            }
            let span = debug_span!("make_action", %terminal);
            let _guard = span.enter();
            let action = self.make_action(visited.clone(), conflicts, invalidate_state)?;
            match terminal {
                Terminal::Token(_, regex) => {
                    regexes.push(regex);
                    actions.push(action);
                }
                Terminal::EndOfInput(ident) => {
                    eoi.insert(ident, action);
                }
            };
        }

        let nfa = NFA::compiler()
            .configure(NFA::config().shrink(true))
            .build_many(&regexes)
            .unwrap();

        validate_nfa(&nfa, &regexes);

        Some(Action::Ambiguous {
            nfa,
            regexes,
            actions,
            eoi,
        })
    }

    fn item_lane_heads(
        &mut self,
        action: ConflictedAction,
        location: ItemIndex,
        transition: Option<Term>,
        split_info: &mut HashMap<Lr0StateId, HashMap<Term, HashMap<NonTerminal, ConflictedAction>>>,
        visited: &mut HashMap<ItemIndex, u32>,
        output: &mut HashSet<(ItemIndex, Option<Term>)>,
    ) -> bool {
        trace!(
            %action,
            %location,
            transition = transition.as_ref().map(|t| t.to_string()),
            "Computing lane heads"
        );
        let (item, back_refs) = &self.lr0_parse_table[location];

        let num_visits = visited.entry(location).or_default();
        // Allow the search to pass through nodes twice so that cycles get counted properly.
        if *num_visits >= 2 {
            return false;
        }
        *num_visits += 1;

        let mut ret = false;
        if let Some(next_state) = &transition {
            let existing_action = split_info
                .entry(location.state_id)
                .or_default()
                .entry(next_state.clone())
                .or_default()
                .entry(item.non_terminal.clone());
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

        if item.index != 0 {
            for item_index in back_refs.clone() {
                let transition = if item_index.state_id == location.state_id {
                    transition.clone()
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
        } else {
            for &back_ref in back_refs {
                let transition = if back_ref.state_id == location.state_id {
                    transition.clone()
                } else {
                    self.lr0_parse_table[back_ref].0.next()
                };
                output.insert((back_ref, transition));
            }
        }
        ret
    }
}

fn conflicts(
    next_state: &Lr0State,
    lr0_state_id: usize,
    grammar: &Grammar,
) -> HashMap<ConflictedAction, Vec<Ambiguity>> {
    let conflicts: HashMap<_, _> = next_state
        .item_set
        .iter()
        .enumerate()
        .filter_map(|(item_idx, (item, _))| {
            let conflict = match item.next() {
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
                    let remaining_negative_lookahead: Vec<_> = item
                        .alternative
                        .negative_lookahead
                        .as_ref()
                        .map(|negative_lookahead| {
                            TermString::new(
                                vec![NormalTerm::NonTerminal(negative_lookahead.clone().into())],
                                0,
                            )
                        })
                        .into_iter()
                        .collect();
                    ConflictedAction::Reduce(
                        item.non_terminal.clone(),
                        item.alternative.clone(),
                        remaining_negative_lookahead,
                    )
                }
            };
            if conflict.contains_finished_lookahead(grammar) {
                // If negative lookahead is finished then this action doesn't exist.
                return None;
            }
            let location = ItemIndex {
                state_id: Lr0StateId(lr0_state_id),
                item: item_idx,
            };
            Some((
                conflict,
                vec![Ambiguity {
                    location,
                    transition: None,
                    history: History::default(),
                    term_string: TermString::new(
                        item.alternative
                            .terms
                            .iter()
                            .cloned()
                            .map(|term| term.kind.into())
                            .collect(),
                        item.index,
                    ),
                }],
            ))
        })
        .collect();
    conflicts
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConflictedAction {
    Shift(Terminal, StateId),
    Reduce(NonTerminal, Alternative, Vec<Arc<TermString>>),
}
impl ConflictedAction {
    fn with_lookahead(&self, grammar: &Grammar, terminal: Terminal) -> ConflictedAction {
        match self {
            ConflictedAction::Reduce(non_terminal, alternative, remaining_negative_lookahead) => {
                let new_negative_lookahead = remaining_negative_lookahead
                    .iter()
                    .flat_map(|term_string| term_string.clone().next(grammar))
                    .filter(|(t, _)| {
                        // Cannot be None because the action should have already
                        // been removed in that case
                        t.as_ref().unwrap() == &terminal
                    })
                    .map(|(_, term_string)| term_string)
                    .collect();
                ConflictedAction::Reduce(
                    non_terminal.clone(),
                    alternative.clone(),
                    new_negative_lookahead,
                )
            }
            other => other.clone(),
        }
    }

    fn contains_finished_lookahead(&self, grammar: &Grammar) -> bool {
        match self {
            ConflictedAction::Shift(_, _) => false,
            ConflictedAction::Reduce(_, _, remaining_negative_lookahead) => {
                remaining_negative_lookahead
                    .iter()
                    .any(|term_string| term_string.clone().next(grammar).any(|(t, _)| t.is_none()))
            }
        }
    }
}

impl fmt::Display for ConflictedAction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConflictedAction::Shift(terminal, id) => {
                write!(f, "Shift({terminal}) -> {id}")?;
            }
            ConflictedAction::Reduce(non_terminal, alternative, remaining_negative_lookahead) => {
                write!(f, "Reduce({non_terminal} -> {alternative}")?;
                for lookahead in remaining_negative_lookahead {
                    write!(f, " (!>> {})", lookahead)?;
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

#[derive(Debug, Clone)]
struct Ambiguity {
    location: ItemIndex,
    transition: Option<Term>,
    history: History,
    term_string: Arc<TermString>,
}

impl fmt::Display for Ambiguity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Ambiguity @ {} ({})", self.location, self.term_string)
    }
}

#[derive(Debug, Default, Clone)]
struct History(Vec<(ItemIndex, TermString)>);

impl fmt::Display for History {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_char('[')?;
        for (i, (location, term_string)) in self.0.iter().enumerate() {
            write!(f, "{} ({})", location, term_string)?;
            if i != self.0.len() - 1 {
                f.write_str(", ")?;
            }
        }
        f.write_char(']')?;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NormalNonTerminal {
    Original(NonTerminal),
    Minus(NonTerminal, TermKind),
}

impl fmt::Display for NormalNonTerminal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (NormalNonTerminal::Original(non_terminal) | NormalNonTerminal::Minus(non_terminal, _)) =
            self;
        write!(f, "{non_terminal}")?;
        if let NormalNonTerminal::Minus(_, minus) = self {
            write!(f, "-{minus}")?;
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
    fn base(&self) -> &NonTerminal {
        match self {
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

impl fmt::Display for NormalTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NormalTerm::Terminal(terminal) => write!(f, "{terminal}"),
            NormalTerm::NonTerminal(non_terminal) => write!(f, "{non_terminal}"),
        }
    }
}

impl From<TermKind> for NormalTerm {
    fn from(t: TermKind) -> Self {
        match t {
            TermKind::Terminal(t) => Self::Terminal(t),
            TermKind::NonTerminal(nt) => Self::NonTerminal(nt.into()),
        }
    }
}

fn normal_production(
    grammar: &Grammar,
    non_terminal: &NormalNonTerminal,
) -> HashSet<Vec<NormalTerm>> {
    let original_production = &grammar.productions[non_terminal.base()];
    match non_terminal {
        NormalNonTerminal::Original(non_terminal) => {
            if left_recursive(grammar, non_terminal.clone()) {
                // 1 - Moor00 5
                proper_left_corners(grammar, non_terminal)
                    .into_iter()
                    .filter(|term| {
                        !matches!(term, TermKind::NonTerminal(nt) if left_recursive(grammar, nt.clone()))
                    })
                    .map(|term| {
                        vec![
                            term.clone().into(),
                            NormalTerm::NonTerminal(NormalNonTerminal::Minus(non_terminal.clone(), term)),
                        ]
                    })
                    .collect()
            } else {
                // 4 - Moor00 5
                original_production
                    .alternatives
                    .iter()
                    .map(|alternative| {
                        alternative
                            .terms
                            .iter()
                            .map(|term| term.kind.clone().into())
                            .collect::<Vec<_>>()
                    })
                    .collect()
            }
        }
        NormalNonTerminal::Minus(non_terminal, symbol) => {
            assert!(left_recursive(grammar, non_terminal.clone()));
            let mut rules = HashSet::new();
            // 3 - Moor00 5
            rules.extend(
                grammar.productions[non_terminal]
                    .alternatives
                    .iter()
                    .filter_map(|alternative| {
                        let mut rule = alternative.terms.iter().map(|term| &term.kind);
                        if rule
                            .by_ref()
                            .find(|term| term == &symbol || !can_be_empty(grammar, term))?
                            != symbol
                        {
                            return None;
                        }
                        // The find call above has eaten all the empty symbols,
                        // so we can just collect the rest of the rule.
                        Some(rule.map(|term| term.clone().into()).collect::<Vec<_>>())
                    }),
            );
            // 2 - Moor00 5
            rules.extend(
                proper_left_corners(grammar, non_terminal)
                    .into_iter()
                    .filter_map(|term| match term {
                        TermKind::NonTerminal(nt) if left_recursive(grammar, nt.clone()) => {
                            Some(nt)
                        }
                        _ => None,
                    })
                    .flat_map(|nt| {
                        grammar.productions[&nt].alternatives.iter().filter_map(
                            move |alternative| {
                                let mut rule = alternative.terms.iter().map(|term| &term.kind);
                                if rule
                                    .by_ref()
                                    .find(|term| term == &symbol || !can_be_empty(grammar, term))?
                                    != symbol
                                {
                                    return None;
                                }
                                // The find call above has eaten all the empty symbols,
                                // so we can just collect the rest of the rule.
                                Some(
                                    rule.map(|term| term.clone().into())
                                        .chain(std::iter::once(NormalTerm::NonTerminal(
                                            NormalNonTerminal::Minus(
                                                non_terminal.clone(),
                                                TermKind::NonTerminal(nt.clone()),
                                            ),
                                        )))
                                        .collect::<Vec<_>>(),
                                )
                            },
                        )
                    }),
            );
            rules
        }
    }
}

fn left_recursive(grammar: &Grammar, non_terminal: NonTerminal) -> bool {
    proper_left_corners(grammar, &non_terminal).contains(&TermKind::NonTerminal(non_terminal))
}

fn proper_left_corners(grammar: &Grammar, non_terminal: &NonTerminal) -> HashSet<TermKind> {
    let mut left_corners = HashSet::new();
    let mut todo = vec![non_terminal.clone()];

    while let Some(nt) = todo.pop() {
        grammar.productions[&nt]
            .alternatives
            .iter()
            .flat_map(|alternative| {
                alternative.terms.iter().scan(true, |prev_empty, term| {
                    let res = prev_empty.then(|| term);
                    *prev_empty = can_be_empty(grammar, &term.kind);
                    res
                })
            })
            .for_each(|term| {
                let new_term = left_corners.insert(term.kind.clone());
                match term.kind.clone() {
                    TermKind::NonTerminal(next) if new_term && &next != non_terminal => {
                        todo.push(next);
                    }
                    _ => {}
                }
            });
    }

    left_corners
}

fn can_be_empty(grammar: &Grammar, term: &TermKind) -> bool {
    fn inner(grammar: &Grammar, term: &TermKind, visited: &mut HashSet<TermKind>) -> bool {
        let TermKind::NonTerminal(nt) = term else {
            return false;
        };
        grammar.productions[nt]
            .alternatives
            .iter()
            .any(|alternative| {
                alternative.terms.iter().all(|term| {
                    if visited.insert(term.kind.clone()) {
                        let res = inner(grammar, &term.kind, visited);
                        visited.remove(&term.kind);
                        res
                    } else {
                        false
                    }
                })
            })
    }
    inner(grammar, term, &mut HashSet::new())
}

/// Check if any of the regexes are prefixes of any of the other regexes.
fn validate_nfa(nfa: &NFA, regexes: &[String]) {
    assert!(nfa.pattern_len() == regexes.len());
    let mut start = BTreeSet::new();
    start.insert(nfa.start_anchored());
    let mut to_visit = vec![(start, None::<PatternID>)];
    let mut visited = HashMap::new();
    while let Some((mut states, mut new_colour)) = to_visit.pop() {
        loop {
            let mut to_add = Vec::new();
            for &id in &states {
                match nfa.state(id) {
                    // This is overzealous and will flag word boundaries etc as
                    // clashing when they actually aren't.
                    &NfaState::Look { look: _, next } => to_add.push(next),
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
        if let Some(old_colour) = visited.get(&states).copied() {
            if let (Some(old_colour), Some(new_colour)) = (old_colour, new_colour) {
                if new_colour != old_colour {
                    panic!(
                        "Conflicting tokens: {} and {}",
                        regexes[old_colour.as_usize()],
                        regexes[new_colour.as_usize()]
                    );
                }
            }
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
                        panic!(
                            "Conflicting tokens: {} and {}",
                            regexes[other_colour.as_usize()],
                            regexes[this_colour.as_usize()]
                        );
                    }
                } else {
                    intrinsic_colour = Some(this_colour);
                }
            }
        }
        if let (Some(intrinsic_colour), Some(new_colour)) = (intrinsic_colour, new_colour) {
            if new_colour != intrinsic_colour {
                panic!(
                    "Conflicting tokens: {} and {}",
                    regexes[intrinsic_colour.as_usize()],
                    regexes[new_colour.as_usize()]
                );
            }
        }
        new_colour = new_colour.or(intrinsic_colour);
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
                to_visit.push((next_states, new_colour));
            }
        }
        visited.insert(states, new_colour);
    }
}
