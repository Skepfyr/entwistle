use std::collections::{HashMap, HashSet, VecDeque};

use itertools::Itertools;
use tracing::instrument;

use super::{
    Ambiguity, Component, ComponentId, ConflictedAction, ItemIndex, Lr0ParseTable, Lr0StateId,
    StronglyConnectedComponents,
};
use crate::{
    diagnostics::{emit, emit_diagnostic, Diagnostic},
    language::Language,
    lower::Terminal,
    Db, Span,
};

pub struct StateSplitter<'a, 'db, F> {
    db: &'db dyn Db,
    language: Language<'db>,
    lr0_parse_table: &'a mut Lr0ParseTable<'db>,
    sccs: &'a mut StronglyConnectedComponents,
    invalidate_state: &'a mut F,
    lookahead_generators: HashMap<ItemIndex, HashSet<ItemIndex>>,
    terminals: HashMap<ItemIndex, HashSet<Terminal<'db>>>,
    conflicting_items: HashMap<(ItemIndex, ItemIndex), Result<(), Vec<Diagnostic>>>,
    component_paths: HashMap<ComponentId, HashMap<Vec<ComponentId>, usize>>,
    components_splits: HashMap<ComponentId, Vec<ComponentId>>,
    old_to_new_state_map: HashMap<(ComponentId, Lr0StateId), Lr0StateId>,
    new_to_old_state_map: HashMap<Lr0StateId, Lr0StateId>,
}

impl<'a, 'db, F: FnMut(Lr0StateId)> StateSplitter<'a, 'db, F> {
    #[instrument(level = "debug", skip_all)]
    pub fn split_states(
        db: &'db dyn Db,
        language: Language<'db>,
        lr0_parse_table: &'a mut Lr0ParseTable<'db>,
        sccs: &'a mut StronglyConnectedComponents,
        conflicts: HashMap<ConflictedAction<'db>, Ambiguity<'db>>,
        invalidate_state: &'a mut F,
        state: Lr0StateId,
    ) -> Option<HashMap<Terminal<'db>, HashMap<ConflictedAction<'db>, Ambiguity<'db>>>> {
        let mut splitter = Self {
            db,
            language,
            lr0_parse_table,
            sccs,
            invalidate_state,
            lookahead_generators: HashMap::new(),
            terminals: HashMap::new(),
            conflicting_items: HashMap::new(),
            component_paths: HashMap::new(),
            components_splits: HashMap::new(),
            old_to_new_state_map: HashMap::new(),
            new_to_old_state_map: HashMap::new(),
        };
        let mut splits = Vec::new();
        let start_locations = conflicts
            .into_iter()
            .flat_map(|(action, ambiguity)| {
                ambiguity
                    .locations
                    .into_iter()
                    .map(|(item, (history, term_string))| {
                        (
                            splitter.sccs.component_map[&item.state_id],
                            (action, history, term_string),
                        )
                    })
            })
            .into_group_map();
        for (component, ambiguities) in start_locations {
            splitter.trace_paths(
                ambiguities,
                component,
                HashMap::new(),
                &mut vec![component],
                &mut splits,
            );
        }
        if splits.len() <= 1 {
            false
        } else {
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
            None
        }
    }

    fn trace_paths(
        &self,
        mut ambiguities: Vec<(VecDeque<Lr0StateId>, ItemIndex, ConflictedAction<'a>)>,
        component: ComponentId,
        mut lookahead: HashMap<ItemIndex, HashSet<ConflictedAction<'a>>>,
        path: &mut Vec<ComponentId>,
        splits: &mut Vec<(
            Option<HashMap<ItemIndex, HashSet<ConflictedAction<'a>>>>,
            Vec<Vec<ComponentId>>,
        )>,
    ) {
        let mut conflicted_locations: HashMap<ItemIndex, HashSet<ConflictedAction>> =
            HashMap::new();
        ambiguities.retain_mut(|(history, loc, action)| {
            while let Some(loc) = history.back() {
                if self.sccs.component(*loc) != component {
                    return true;
                }
                history.pop_back();
            }
            conflicted_locations
                .entry(*loc)
                .or_default()
                .insert(action.clone());
            false
        });
        for (loc, actions) in &conflicted_locations {
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
        lookahead.extend(conflicted_locations);

        if !ambiguities.is_empty() {
            for &next_component in self.sccs.back_refs(component) {
                let ambiguities = ambiguities
                    .iter()
                    .filter(|(history, _, _)| {
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
            for &item_a in lookahead.keys() {
                for &item_b in lookahead.keys() {
                    if item_a == item_b {
                        continue;
                    }
                    if self.items_conflict(item_a, item_b, true) {
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
                    for (&item, action) in &lookahead {
                        if let Some(split_action) = split_lookahead.get(&item) {
                            if action != split_action {
                                return false;
                            }
                        } else {
                            for &split_item in split_lookahead.keys() {
                                if self.items_conflict(item, split_item, false) {
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

    fn items_conflict(&self, item_a: ItemIndex, item_b: ItemIndex, emit: bool) -> bool {
        let [item_a, item_b] = {
            let mut items = [item_a, item_b];
            items.sort();
            items
        };
        if let Some(diags) = self
            .conflicting_items
            .borrow_mut()
            .get_mut(&(item_a, item_b))
        {
            if emit {
                if let Err(diags) = diags {
                    for diag in std::mem::take(diags) {
                        emit_diagnostic(diag);
                    }
                }
            }
            return diags.is_err();
        }
        let terminals_a = self
            .terminals
            .get(&item_a)
            .expect("All items should have terminals");
        let terminals_b = self
            .terminals
            .get(&item_b)
            .expect("All items should have terminals");
        #[allow(clippy::manual_try_fold)]
        let conflicts = terminals_a
            .iter()
            .cartesian_product(terminals_b)
            .filter(|(a, b)| a != b)
            .fold(Ok(()), |acc, (terminal_a, terminal_b)| {
                match (
                    acc,
                    terminals_conflict(
                        self.db,
                        self.language,
                        terminal_a.clone(),
                        terminal_b.clone(),
                    ),
                ) {
                    (Ok(()), Ok(())) => Ok(()),
                    (Ok(()), Err(diag)) => Err(if emit {
                        emit_diagnostic(diag);
                        vec![]
                    } else {
                        vec![diag]
                    }),
                    (acc @ Err(_), Ok(())) => acc,
                    (Err(mut diags), Err(diag)) => {
                        if emit {
                            emit_diagnostic(diag);
                        } else {
                            diags.push(diag);
                        }
                        Err(diags)
                    }
                }
            });
        let result = conflicts.is_err();
        self.conflicting_items
            .borrow_mut()
            .insert((item_a, item_b), conflicts);
        result
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
