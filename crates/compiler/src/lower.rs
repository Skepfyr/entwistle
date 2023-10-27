use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt::{self, Write as _},
    hash::Hash,
    ops::RangeInclusive,
    sync::Arc,
};

use regex_automata::{
    nfa::thompson::{
        Builder as NfaBuilder, DenseTransitions, SparseTransitions, Transition, WhichCaptures, NFA,
    },
    util::{look::Look, primitives::StateID, syntax},
    PatternID,
};
use regex_syntax::hir::Hir;
use tracing::instrument;

use crate::{
    diagnostics::emit,
    language::{Expression, Ident, Item, Language, Mark, Quantifier, Rule},
    Span,
};

#[instrument(skip_all, fields(%non_terminal))]
pub fn production(language: &Language, non_terminal: &NonTerminalUse) -> Production {
    match non_terminal {
        NonTerminalUse::Goal { rule } => Production {
            alternatives: vec![Alternative {
                span: non_terminal.span(),
                terms: vec![
                    Term {
                        kind: TermKind::NonTerminal(NonTerminalUse::Anonymous {
                            rule: rule.clone(),
                            context: None,
                            generics: BTreeMap::new(),
                        }),
                        silent: true,
                    },
                    Term {
                        kind: TermKind::Terminal(TerminalUse::EndOfInput {
                            span: Span {
                                start: non_terminal.span().end,
                                end: non_terminal.span().end,
                            },
                        }),
                        silent: true,
                    },
                ],
                negative_lookahead: None,
            }],
        },
        NonTerminalUse::Named {
            name,
            generics: generic_parameters,
            span,
        } => {
            let definition = &language.definitions[&name.ident];
            assert!(!definition.atomic, "Tried to make production for terminal");
            if definition.generics.len() != generic_parameters.len() {
                emit(
                    format!(
                        "Expected {} generics, found {}",
                        definition.generics.len(),
                        generic_parameters.len()
                    ),
                    vec![(*span, None)],
                );
                return Production {
                    alternatives: vec![],
                };
            }
            let generics = std::iter::Iterator::zip(
                definition.generics.iter().cloned(),
                generic_parameters.iter().cloned(),
            )
            .collect();
            if definition.rules.is_empty() {
                if name.index > 0 {
                    // ICE
                    panic!(
                        "Unexpected index {} for empty definition for {}",
                        name.index, name.ident
                    );
                }
                return Production {
                    alternatives: vec![],
                };
            }
            fn contains_this_sub(this: &Ident, rule: &Rule) -> (bool, bool) {
                let mut contains_this = false;
                let mut contains_sub = false;
                for alternative in &rule.alternatives {
                    for (item, _, _) in &alternative.sequence {
                        match item {
                            Item::Ident {
                                mark,
                                ident,
                                generics: _,
                            } if ident == this => {
                                contains_this |= mark == &Mark::This;
                                contains_sub |= mark == &Mark::Sub;
                            }
                            Item::Group(inner_rule) => {
                                let (this, sub) = contains_this_sub(this, inner_rule);
                                contains_this |= this;
                                contains_sub |= sub;
                            }
                            _ => {}
                        }
                        if contains_this && contains_sub {
                            return (true, true);
                        }
                    }
                }
                (contains_this, contains_sub)
            }
            // Whether this rule contains a split below it.
            let splits = definition
                .rules
                .iter()
                .map(|rule| contains_this_sub(&name.ident, rule))
                .chain(Some((false, false)))
                .scan(false, |prev_split_below, (this, sub)| {
                    let split_above = *prev_split_below || this;
                    *prev_split_below = sub;
                    Some(split_above)
                })
                .skip(1);
            let mut index = name.index;
            let mut first = 0;
            let mut last = 0;
            for (i, split_below) in splits.enumerate() {
                last = i + 1;
                if split_below {
                    if index == 0 {
                        break;
                    }
                    index -= 1;
                    first = last;
                }
            }
            if index > 0 {
                // ICE
                panic!("Index {} out of bounds for {}", name.index, name.ident);
            }
            let mut alternatives: Vec<_> = definition.rules[first..last]
                .iter()
                .flat_map(|rule| lower_rule(language, rule, Some(name), &generics).alternatives)
                .collect();
            if last != definition.rules.len() {
                let span = Span {
                    start: definition.rules[first].span.start,
                    end: definition.rules[last - 1].span.end,
                };
                alternatives.push(Alternative {
                    span,
                    terms: vec![Term {
                        kind: TermKind::NonTerminal(NonTerminalUse::Named {
                            name: Name {
                                ident: name.ident.clone(),
                                index: name.index + 1,
                            },
                            generics: generic_parameters.clone(),
                            span,
                        }),
                        silent: true,
                    }],
                    negative_lookahead: None,
                });
            }
            Production { alternatives }
        }
        NonTerminalUse::Anonymous {
            rule,
            context,
            generics,
        } => {
            if rule.alternatives.len() == 1
                && rule.alternatives.iter().next().unwrap().sequence.len() == 1
            {
                let &(ref item, ref quantifier, span) =
                    &rule.alternatives.iter().next().unwrap().sequence[0];
                let term = lower_term(
                    language,
                    generics,
                    item,
                    Quantifier::Once,
                    span,
                    context.as_ref(),
                );
                let mut alternatives: Vec<Alternative> = Vec::new();
                // Zero times
                if let Quantifier::Any | Quantifier::AtMostOnce = quantifier {
                    alternatives.push(Alternative {
                        span,
                        terms: vec![],
                        negative_lookahead: None,
                    });
                }
                // One time
                if let Quantifier::AtMostOnce | Quantifier::AtLeastOnce | Quantifier::Once =
                    quantifier
                {
                    alternatives.push(Alternative {
                        span,
                        terms: vec![term.clone()],
                        negative_lookahead: None,
                    });
                }
                // Many times
                if let Quantifier::Any | Quantifier::AtLeastOnce = quantifier {
                    alternatives.push(Alternative {
                        span,
                        terms: vec![
                            Term {
                                kind: TermKind::NonTerminal(non_terminal.clone()),
                                silent: true,
                            },
                            term,
                        ],
                        negative_lookahead: None,
                    });
                }
                Production { alternatives }
            } else {
                lower_rule(language, rule, context.as_ref(), generics)
            }
        }
    }
}

#[instrument(skip_all, fields(%rule, ?current_name, ?generics))]
fn lower_rule(
    language: &Language,
    rule: &Rule,
    current_name: Option<&Name>,
    generics: &BTreeMap<Ident, NonTerminalUse>,
) -> Production {
    Production {
        alternatives: rule
            .alternatives
            .iter()
            .map(|expression| {
                let (sequence, lookahead) = match expression.sequence.last() {
                    Some((Item::Lookaround(lookaround_type, rule), quantifier, _)) => {
                        if *quantifier != Quantifier::Once {
                            emit(
                                "Lookaround cannot have a quantifier",
                                vec![(lookaround_type.span, None)],
                            );
                        }
                        let sequence = &expression.sequence[..expression.sequence.len() - 1];
                        if lookaround_type.positive || !lookaround_type.ahead {
                            emit(
                                "Only negative lookahead is supported",
                                vec![(lookaround_type.span, None)],
                            );
                            (sequence, None)
                        } else {
                            (
                                sequence,
                                Some(NonTerminalUse::new_anonymous(
                                    rule.clone(),
                                    current_name,
                                    generics.clone(),
                                )),
                            )
                        }
                    }
                    _ => (&expression.sequence[..], None),
                };
                let terms = sequence
                    .iter()
                    .map(|(term, quantifier, span)| {
                        lower_term(language, generics, term, *quantifier, *span, current_name)
                    })
                    .collect::<Vec<_>>();
                Alternative {
                    span: expression.span,
                    terms,
                    negative_lookahead: lookahead,
                }
            })
            .collect(),
    }
}

#[instrument(skip_all, fields(%item, %quantifier, %span, ?current_name, ?generics))]
fn lower_term(
    language: &Language,
    generics: &BTreeMap<Ident, NonTerminalUse>,
    item: &Item,
    quantifier: Quantifier,
    span: Span,
    current_name: Option<&Name>,
) -> Term {
    if quantifier != Quantifier::Once {
        let mut alternatives = BTreeSet::new();
        alternatives.insert(Expression {
            sequence: vec![(item.clone(), quantifier, span)],
            span,
        });
        return Term {
            kind: TermKind::NonTerminal(NonTerminalUse::new_anonymous(
                Rule { alternatives, span },
                current_name,
                generics.clone(),
            )),
            silent: true,
        };
    }

    match item {
        Item::Ident {
            mark,
            ident,
            generics: generic_arguments,
        } => match generics.get(ident) {
            Some(nt) => Term {
                kind: TermKind::NonTerminal(nt.clone()),
                silent: true,
            },
            None => {
                let definition = match language.definitions.get(ident) {
                    Some(definition) => definition,
                    None => {
                        emit("This identifier is not defined", vec![(span, None)]);
                        return Term {
                            kind: TermKind::NonTerminal(NonTerminalUse::Anonymous {
                                rule: Rule {
                                    span,
                                    alternatives: BTreeSet::new(),
                                },
                                context: None,
                                generics: BTreeMap::new(),
                            }),
                            silent: true,
                        };
                    }
                };
                let kind = if definition.atomic {
                    TermKind::Terminal(TerminalUse::Named {
                        ident: ident.clone(),
                        span,
                    })
                } else {
                    let name = match current_name {
                        Some(current_name) if ident == &current_name.ident => Name {
                            ident: current_name.ident.clone(),
                            index: match mark {
                                Mark::Super => 0,
                                Mark::This => current_name.index,
                                Mark::Sub => current_name.index + 1,
                            },
                        },
                        _ => Name {
                            ident: ident.clone(),
                            index: 0,
                        },
                    };
                    let generic_parameters = generic_arguments
                        .iter()
                        .map(|arg| {
                            NonTerminalUse::new_anonymous(
                                arg.clone(),
                                current_name,
                                generics.clone(),
                            )
                        })
                        .collect();
                    TermKind::NonTerminal(NonTerminalUse::Named {
                        name,
                        generics: generic_parameters,
                        span,
                    })
                };
                Term {
                    kind,
                    silent: definition.silent,
                }
            }
        },
        Item::String(data) => Term {
            kind: TermKind::Terminal(TerminalUse::Anonymous {
                name: Arc::from(&**data),
                regex: NFA::compiler()
                    .build_from_hir(&Hir::literal(data.as_bytes()))
                    .unwrap(),
                span,
            }),
            silent: false,
        },
        Item::Regex(regex) => Term {
            kind: TermKind::Terminal(TerminalUse::Anonymous {
                name: Arc::from(&**regex),
                regex: regex_nfa(regex, span),
                span,
            }),
            silent: false,
        },
        Item::Group(rule) => Term {
            kind: TermKind::NonTerminal(NonTerminalUse::new_anonymous(
                rule.clone(),
                current_name,
                generics.clone(),
            )),
            silent: true,
        },
        Item::Lookaround(_, _) => {
            emit(
                "Only negative lookahead is supported and only at the end of an expression",
                vec![(span, None)],
            );
            Term {
                kind: TermKind::NonTerminal(NonTerminalUse::Anonymous {
                    rule: Rule {
                        span,
                        alternatives: BTreeSet::new(),
                    },
                    context: None,
                    generics: BTreeMap::new(),
                }),
                silent: true,
            }
        }
    }
}

#[instrument(skip_all, fields(%terminal))]
pub fn terminal_nfa(language: &Language, terminal: &TerminalDef) -> NFA {
    match terminal {
        TerminalDef::Named { ident, span } => {
            let nfa = ident_nfa(language, ident, *span, &mut HashSet::new());
            if nfa.has_empty() {
                emit(
                    "Tokens must not match the empty string",
                    vec![(*span, None)],
                );
            }
            nfa
        }
        TerminalDef::Anonymous { regex, .. } => regex.clone(),
        TerminalDef::EndOfInput => NFA::compiler()
            .build_from_hir(&Hir::look(regex_syntax::hir::Look::End))
            .unwrap(),
    }
}

#[instrument(skip_all, fields(%ident))]
fn ident_nfa(language: &Language, ident: &Ident, span: Span, visited: &mut HashSet<Ident>) -> NFA {
    if !visited.insert(ident.clone()) {
        emit(
            "Recursive atomic rules are not (yet) supported",
            vec![(span, None)],
        );
        return NFA::never_match();
    }
    let Some(definition) = language.definitions.get(ident) else {
        emit("Definition not found", vec![(span, None)]);
        return NFA::never_match();
    };
    if !definition.atomic {
        emit("Non-atomic rule used by atomic rule", vec![(span, None)]);
        return NFA::never_match();
    }
    if !definition.generics.is_empty() {
        emit(
            "Generics are not supported on atomic rules",
            vec![(definition.span, None)],
        );
        return NFA::never_match();
    }

    let nfa = alternation(
        definition
            .rules
            .iter()
            .map(|rule| rule_nfa(language, rule, visited)),
    );
    visited.remove(ident);
    nfa
}

#[instrument(skip_all, fields(%rule))]
fn rule_nfa(language: &Language, rule: &Rule, visited: &mut HashSet<Ident>) -> NFA {
    alternation(
        rule.alternatives
            .iter()
            .map(|expression| expression_nfa(language, expression, visited)),
    )
}

fn alternation(alternatives: impl Iterator<Item = NFA>) -> NFA {
    let mut builder = NfaBuilder::new();
    builder.set_utf8(true);
    builder.start_pattern().unwrap();
    let mat = builder.add_match().unwrap();
    let end = builder.add_capture_end(mat, 0).unwrap();
    let alternates = alternatives
        .map(|nfa| prepend_nfa(&mut builder, end, &nfa))
        .collect();
    let alt_start = builder.add_union(alternates).unwrap();
    let start = builder.add_capture_start(alt_start, 0, None).unwrap();
    builder.finish_pattern(start).unwrap();
    builder.build(start, start).unwrap()
}

#[instrument(skip_all, fields(%expression))]
fn expression_nfa(
    language: &Language,
    expression: &Expression,
    visited: &mut HashSet<Ident>,
) -> NFA {
    let mut builder = NfaBuilder::new();
    builder.set_utf8(true);
    builder.start_pattern().unwrap();
    let mat = builder.add_match().unwrap();
    let mut start = builder.add_capture_end(mat, 0).unwrap();
    for (item, quantifier, span) in expression.sequence.iter().rev() {
        let item = match item {
            Item::Ident {
                mark,
                ident,
                generics,
            } => {
                if *mark != Mark::This {
                    emit(
                        "Marks are not supported in atomic rules",
                        vec![(*span, None)],
                    );
                }
                if !generics.is_empty() {
                    emit(
                        "Generics are not supported in atomic rules",
                        vec![(*span, None)],
                    );
                }
                ident_nfa(language, ident, *span, visited)
            }
            Item::String(string) => NFA::compiler()
                .build_from_hir(&Hir::literal(string.as_bytes()))
                .unwrap(),
            Item::Regex(regex) => regex_nfa(regex, *span),
            Item::Group(rule) => rule_nfa(language, rule, visited),
            Item::Lookaround(lookaround_type, rule) => {
                if !lookaround_type.ahead || lookaround_type.positive {
                    emit(
                        "Only negative lookahead is supported",
                        vec![(lookaround_type.span, None)],
                    );
                    continue;
                }

                start = builder.add_capture_start(start, 0, None).unwrap();
                builder.finish_pattern(start).unwrap();
                let tail = builder.build(start, start).unwrap();
                // Restart the builder from the beginning
                builder = NfaBuilder::new();
                builder.set_utf8(true);
                builder.start_pattern().unwrap();
                let mat = builder.add_match().unwrap();
                start = builder.add_capture_end(mat, 0).unwrap();
                let rule = rule_nfa(language, rule, visited);
                subtract_nfa(&tail, &rule)
            }
        };
        match quantifier {
            Quantifier::Once => {
                start = prepend_nfa(&mut builder, start, &item);
            }
            Quantifier::AtMostOnce => {
                let end = start;
                start = prepend_nfa(&mut builder, start, &item);
                start = builder.add_union(vec![start, end]).unwrap();
            }
            Quantifier::AtLeastOnce => {
                let repeat_end = builder.add_union(vec![start]).unwrap();
                start = prepend_nfa(&mut builder, repeat_end, &item);
                builder.patch(repeat_end, start).unwrap();
            }
            Quantifier::Any => {
                let end = start;
                let repeat_end = builder.add_union(vec![start]).unwrap();
                let repeat_start = prepend_nfa(&mut builder, repeat_end, &item);
                builder.patch(repeat_end, repeat_start).unwrap();
                start = builder.add_union(vec![repeat_start, end]).unwrap();
            }
        }
    }
    let start = builder.add_capture_start(start, 0, None).unwrap();
    builder.finish_pattern(start).unwrap();
    builder.build(start, start).unwrap()
}

fn prepend_nfa(builder: &mut NfaBuilder, start: StateID, nfa: &NFA) -> StateID {
    use regex_automata::nfa::thompson::State;
    let mut state_map: HashMap<StateID, StateID> = HashMap::new();
    let map_state = |builder: &mut NfaBuilder,
                     state_map: &mut HashMap<StateID, StateID>,
                     state: StateID|
     -> StateID {
        *state_map.entry(state).or_insert_with_key(|state| {
            match nfa.state(*state) {
                State::ByteRange { trans } => builder
                    .add_range(Transition {
                        start: trans.start,
                        end: trans.end,
                        next: StateID::MAX,
                    })
                    .unwrap(),
                State::Sparse(_) | State::Dense(_) => {
                    // Sparse states can't be patched so indirect though an empty state
                    builder.add_empty().unwrap()
                }
                State::Look { look, .. } => builder.add_look(StateID::MAX, *look).unwrap(),
                State::Union { alternates } => builder
                    .add_union(Vec::with_capacity(alternates.len()))
                    .unwrap(),
                State::BinaryUnion { .. } => builder.add_union(Vec::with_capacity(2)).unwrap(),
                State::Capture { .. } => {
                    // Ignore capture states as they'll conflict with this NFA's captures.
                    builder.add_empty().unwrap()
                }
                State::Fail => builder.add_fail().unwrap(),
                State::Match { pattern_id } => {
                    if *pattern_id != PatternID::ZERO {
                        panic!("Terminal regexes shouldn't use patterns")
                    }
                    start
                }
            }
        })
    };
    for (old_id, state) in nfa.states().iter().enumerate().rev() {
        let new_id = map_state(builder, &mut state_map, StateID::new(old_id).unwrap());
        match state {
            State::ByteRange { trans } => {
                let next = map_state(builder, &mut state_map, trans.next);
                builder.patch(new_id, next).unwrap()
            }
            State::Sparse(SparseTransitions { transitions }) => {
                let transitions = transitions
                    .iter()
                    .map(|trans| Transition {
                        start: trans.start,
                        end: trans.end,
                        next: map_state(builder, &mut state_map, trans.next),
                    })
                    .collect();
                let state = builder.add_sparse(transitions).unwrap();
                builder.patch(new_id, state).unwrap();
            }
            State::Dense(DenseTransitions { transitions }) => {
                let transitions = transitions
                    .iter()
                    .enumerate()
                    .map(|(i, state)| Transition {
                        start: i as u8,
                        end: i as u8,
                        next: map_state(builder, &mut state_map, *state),
                    })
                    .collect();
                let state = builder.add_sparse(transitions).unwrap();
                builder.patch(new_id, state).unwrap();
            }
            State::Look { next, .. } => {
                let next = map_state(builder, &mut state_map, *next);
                builder.patch(new_id, next).unwrap()
            }
            State::Union { alternates } => {
                for state in alternates.iter() {
                    let alternate = map_state(builder, &mut state_map, *state);
                    builder.patch(new_id, alternate).unwrap()
                }
            }
            State::BinaryUnion { alt1, alt2 } => {
                let alt1 = map_state(builder, &mut state_map, *alt1);
                let alt2 = map_state(builder, &mut state_map, *alt2);
                builder.patch(new_id, alt1).unwrap();
                builder.patch(new_id, alt2).unwrap();
            }
            State::Capture { next, .. } => {
                let next = map_state(builder, &mut state_map, *next);
                builder.patch(new_id, next).unwrap();
            }
            State::Fail => {}
            State::Match { .. } => {}
        }
    }
    state_map[&nfa.start_anchored()]
}

fn subtract_nfa(a: &NFA, b: &NFA) -> NFA {
    let mut builder = NfaBuilder::new();
    builder.set_utf8(true);
    builder.start_pattern().unwrap();
    let start = builder.add_capture_start(StateID::MAX, 0, None).unwrap();

    let mut state_map = HashMap::<(StateID, (BTreeSet<StateID>, bool)), StateID>::new();
    let mut states = BTreeSet::new();
    states.insert(b.start_anchored());

    build_subtracted_nfa(
        &mut state_map,
        &mut builder,
        start,
        a,
        a.start_anchored(),
        b,
        states,
        false,
    );

    builder.finish_pattern(start).unwrap();
    builder.build(start, start).unwrap()
}

fn build_subtracted_nfa(
    state_map: &mut HashMap<(StateID, (BTreeSet<StateID>, bool)), StateID>,
    builder: &mut NfaBuilder,
    prev_loc: StateID,
    a: &NFA,
    a_loc: StateID,
    b: &NFA,
    b_loc: BTreeSet<StateID>,
    b_match: bool,
) {
    let mut closure = HashMap::new();
    closure.insert(None, Default::default());
    let mut visited = HashSet::new();
    for loc in b_loc {
        nfa_epsilon_closure(&mut visited, b, loc, &mut closure, None);
    }

    let closures = match closure.len() {
        0 => unreachable!(),
        1 => {
            let mut b_loc = closure.remove(&None).unwrap();
            b_loc.1 |= b_match;
            vec![(b_loc, prev_loc)]
        }
        2 => {
            let mut no_look = closure.remove(&None).unwrap();
            no_look.1 |= b_match;
            let (look, mut loc) = closure.into_iter().next().unwrap();
            loc.0.extend(&no_look.0);
            loc.1 |= no_look.1;
            let positive_look = Look::from_repr(look.unwrap()).unwrap();
            let positive_state = builder.add_look(StateID::MAX, positive_look).unwrap();
            let split_state = builder.add_union(vec![positive_state]).unwrap();
            builder.patch(prev_loc, split_state).unwrap();
            let negative_state = match positive_look {
                Look::Start
                | Look::End
                | Look::StartLF
                | Look::EndLF
                | Look::StartCRLF
                | Look::EndCRLF
                | Look::WordStartHalfAscii
                | Look::WordEndHalfAscii
                | Look::WordStartHalfUnicode
                | Look::WordEndHalfUnicode => todo!("Unclear how to negate these"),
                Look::WordAscii => {
                    let state = builder
                        .add_look(StateID::MAX, Look::WordAsciiNegate)
                        .unwrap();
                    builder.patch(split_state, state).unwrap();
                    state
                }
                Look::WordAsciiNegate => {
                    let state = builder.add_look(StateID::MAX, Look::WordAscii).unwrap();
                    builder.patch(split_state, state).unwrap();
                    state
                }
                Look::WordUnicode => {
                    let state = builder
                        .add_look(StateID::MAX, Look::WordUnicodeNegate)
                        .unwrap();
                    builder.patch(split_state, state).unwrap();
                    state
                }
                Look::WordUnicodeNegate => {
                    let state = builder.add_look(StateID::MAX, Look::WordUnicode).unwrap();
                    builder.patch(split_state, state).unwrap();
                    state
                }
                Look::WordStartAscii => {
                    // The opposite of the start of a word is the end of a word or not a word boundary.
                    let state = builder.add_empty().unwrap();
                    let word_ascii_negate = builder.add_look(state, Look::WordAsciiNegate).unwrap();
                    builder.patch(word_ascii_negate, state).unwrap();
                    let word_end_ascii = builder.add_look(state, Look::WordEndAscii).unwrap();
                    builder.patch(word_end_ascii, state).unwrap();
                    state
                }
                Look::WordEndAscii => {
                    // The opposite of the end of a word is the start of a word or not a word boundary.
                    let state = builder.add_empty().unwrap();
                    let word_ascii_negate = builder.add_look(state, Look::WordAsciiNegate).unwrap();
                    builder.patch(word_ascii_negate, state).unwrap();
                    let word_start_ascii = builder.add_look(state, Look::WordStartAscii).unwrap();
                    builder.patch(word_start_ascii, state).unwrap();
                    state
                }
                Look::WordStartUnicode => {
                    // The opposite of the start of a word is the end of a word or not a word boundary.
                    let state = builder.add_empty().unwrap();
                    let word_unicode_negate =
                        builder.add_look(state, Look::WordUnicodeNegate).unwrap();
                    builder.patch(word_unicode_negate, state).unwrap();
                    let word_end_unicode = builder.add_look(state, Look::WordEndUnicode).unwrap();
                    builder.patch(word_end_unicode, state).unwrap();
                    state
                }
                Look::WordEndUnicode => {
                    // The opposite of the end of a word is the start of a word or not a word boundary.
                    let state = builder.add_empty().unwrap();
                    let word_unicode_negate =
                        builder.add_look(state, Look::WordUnicodeNegate).unwrap();
                    builder.patch(word_unicode_negate, state).unwrap();
                    let word_start_unicode =
                        builder.add_look(state, Look::WordStartUnicode).unwrap();
                    builder.patch(word_start_unicode, state).unwrap();
                    state
                }
            };
            vec![(loc, positive_state), (no_look, negative_state)]
        }
        _ => {
            panic!("Only one form of lookaround supported at once in atomic negation");
        }
    };

    for ((b_loc, b_match), prev_loc) in closures {
        use std::collections::hash_map::Entry;
        let loc = match state_map.entry((a_loc, (b_loc.clone(), b_match))) {
            Entry::Occupied(entry) => {
                builder.patch(prev_loc, *entry.get()).unwrap();
                // The state has already been built so skip.
                continue;
            }
            Entry::Vacant(entry) => {
                let loc = builder.add_empty().unwrap();
                entry.insert(loc);
                builder.patch(prev_loc, loc).unwrap();
                loc
            }
        };
        use regex_automata::nfa::thompson::State;
        let implementation = match a.state(a_loc) {
            State::ByteRange { trans } => {
                let transitions = transition(b, &b_loc, trans.start..=trans.end)
                    .map(|(b_loc, range)| {
                        let next = builder.add_empty().unwrap();
                        build_subtracted_nfa(
                            state_map, builder, next, a, trans.next, b, b_loc, false,
                        );
                        Transition {
                            start: *range.start(),
                            end: *range.end(),
                            next,
                        }
                    })
                    .collect();
                builder.add_sparse(transitions).unwrap()
            }
            State::Sparse(SparseTransitions { transitions }) => {
                let transitions = transitions
                    .iter()
                    .flat_map(|trans| {
                        transition(b, &b_loc, trans.start..=trans.end)
                            .map(|(b_loc, range)| (trans.next, b_loc, range))
                    })
                    .map(|(a_loc, b_loc, range)| {
                        let next = builder.add_empty().unwrap();
                        build_subtracted_nfa(state_map, builder, next, a, a_loc, b, b_loc, false);
                        Transition {
                            start: *range.start(),
                            end: *range.end(),
                            next,
                        }
                    })
                    .collect();
                builder.add_sparse(transitions).unwrap()
            }
            State::Dense(DenseTransitions { transitions }) => {
                let transitions = transitions
                    .iter()
                    .enumerate()
                    .flat_map(|(i, next)| {
                        let i = i.try_into().unwrap();
                        transition(b, &b_loc, i..=i).map(|(b_loc, range)| (*next, b_loc, range))
                    })
                    .map(|(a_loc, b_loc, range)| {
                        let next = builder.add_empty().unwrap();
                        build_subtracted_nfa(state_map, builder, next, a, a_loc, b, b_loc, false);
                        Transition {
                            start: *range.start(),
                            end: *range.end(),
                            next,
                        }
                    })
                    .collect();
                builder.add_sparse(transitions).unwrap()
            }
            State::Look { look, next } => {
                let implementation = builder.add_look(StateID::MAX, *look).unwrap();
                build_subtracted_nfa(
                    state_map,
                    builder,
                    implementation,
                    a,
                    *next,
                    b,
                    b_loc,
                    b_match,
                );
                implementation
            }
            State::Union { alternates } => {
                let implementation = builder.add_union(Vec::with_capacity(2)).unwrap();
                for &a_alt in &**alternates {
                    let alt = builder.add_empty().unwrap();
                    build_subtracted_nfa(
                        state_map,
                        builder,
                        alt,
                        a,
                        a_alt,
                        b,
                        b_loc.clone(),
                        b_match,
                    );
                    builder.patch(implementation, alt).unwrap();
                }
                implementation
            }
            State::BinaryUnion { alt1, alt2 } => {
                let implementation = builder.add_union(Vec::with_capacity(2)).unwrap();
                for &a_alt in [alt1, alt2] {
                    let alt = builder.add_empty().unwrap();
                    build_subtracted_nfa(
                        state_map,
                        builder,
                        alt,
                        a,
                        a_alt,
                        b,
                        b_loc.clone(),
                        b_match,
                    );
                    builder.patch(implementation, alt).unwrap();
                }
                implementation
            }
            State::Capture {
                next,
                pattern_id: _,
                group_index: _,
                slot: _,
            } => {
                let new = builder.add_empty().unwrap();
                build_subtracted_nfa(state_map, builder, new, a, *next, b, b_loc, b_match);
                new
            }
            State::Fail => builder.add_fail().unwrap(),
            State::Match { pattern_id: _ } => {
                if b_match {
                    builder.add_fail().unwrap()
                } else {
                    let match_state = builder.add_match().unwrap();
                    builder.add_capture_end(match_state, 0).unwrap()
                }
            }
        };
        builder.patch(loc, implementation).unwrap();
    }
}

fn nfa_epsilon_closure(
    visited: &mut HashSet<StateID>,
    nfa: &NFA,
    state: StateID,
    closure: &mut HashMap<Option<u32>, (BTreeSet<StateID>, bool)>,
    look: Option<Look>,
) {
    use regex_automata::nfa::thompson::State;

    if !visited.insert(state) {
        return;
    }

    match nfa.state(state) {
        State::Look {
            look: new_look,
            next,
        } => match (look, new_look) {
            (None, look) => nfa_epsilon_closure(visited, nfa, *next, closure, Some(*look)),
            (Some(look), new_look) if look == *new_look => {
                nfa_epsilon_closure(visited, nfa, *next, closure, Some(look))
            }
            (Some(look), new_look) => {
                panic!(
                    "Atomic negation doesn't (yet) support simultaneous {} and {}",
                    look.as_char(),
                    new_look.as_char()
                );
            }
        },
        State::Capture { next, .. } => nfa_epsilon_closure(visited, nfa, *next, closure, look),
        State::Union { alternates } => {
            for state in alternates.iter() {
                nfa_epsilon_closure(visited, nfa, *state, closure, look)
            }
        }
        State::BinaryUnion { alt1, alt2 } => {
            nfa_epsilon_closure(visited, nfa, *alt1, closure, look);
            nfa_epsilon_closure(visited, nfa, *alt2, closure, look);
        }
        State::Fail => {}
        State::ByteRange { .. } | State::Sparse(_) | State::Dense(_) => {
            closure
                .entry(look.map(Look::as_repr))
                .or_default()
                .0
                .insert(state);
        }
        State::Match { .. } => {
            closure.entry(look.map(Look::as_repr)).or_default().1 = true;
        }
    }
}

fn transition(
    nfa: &NFA,
    loc: &BTreeSet<StateID>,
    bytes: RangeInclusive<u8>,
) -> impl Iterator<Item = (BTreeSet<StateID>, RangeInclusive<u8>)> {
    let mut locs = BTreeMap::new();
    locs.insert(*bytes.start(), (BTreeSet::new(), bytes));
    for &state in loc {
        use regex_automata::nfa::thompson::State;
        let transitions = match nfa.state(state) {
            State::ByteRange { trans } => vec![*trans],
            State::Sparse(SparseTransitions { transitions }) => transitions.to_vec(),
            State::Dense(DenseTransitions { transitions }) => transitions
                .iter()
                .enumerate()
                .map(|(i, trans)| {
                    let i = i.try_into().unwrap();
                    Transition {
                        start: i,
                        end: i,
                        next: *trans,
                    }
                })
                .collect(),
            State::Look { .. }
            | State::Union { .. }
            | State::BinaryUnion { .. }
            | State::Capture { .. }
            | State::Fail
            | State::Match { .. } => panic!("Only non-epsilon states expected"),
        };
        for transition in transitions {
            let start = match locs.range(..=transition.start).next_back() {
                Some((_, (_, range))) => {
                    let range = range.clone();
                    if *range.start() < transition.start && transition.start <= *range.end() {
                        let (loc, range) = locs.remove(range.start()).unwrap();
                        locs.insert(
                            *range.start(),
                            (loc.clone(), *range.start()..=transition.start - 1),
                        );
                        locs.insert(transition.start, (loc, transition.start..=*range.end()));
                    }
                    transition.start
                }
                None => *locs.keys().next().unwrap(),
            };
            let end = match locs.range(..=transition.end).next_back() {
                Some((_, (_, range))) => {
                    let range = range.clone();
                    if *range.start() <= transition.end && transition.end < *range.end() {
                        let (loc, range) = locs.remove(range.start()).unwrap();
                        locs.insert(
                            *range.start(),
                            (loc.clone(), *range.start()..=transition.end),
                        );
                        locs.insert(transition.end + 1, (loc, transition.end + 1..=*range.end()));
                    }
                    transition.end
                }
                None => continue,
            };
            for (_, (loc, _)) in locs.range_mut(start..=end) {
                loc.insert(transition.next);
            }
        }
    }
    locs.into_values()
}

#[instrument(skip_all, fields(%regex))]
fn regex_nfa(regex: &str, span: Span) -> NFA {
    let nfa = NFA::compiler()
        .configure(NFA::config().which_captures(WhichCaptures::Implicit))
        .syntax(syntax::Config::default().unicode(true))
        .build(regex)
        .unwrap_or_else(|err| {
            let mut reason = err.to_string();
            let mut err = &err as &dyn std::error::Error;
            loop {
                err = match err.source() {
                    Some(err) => err,
                    None => break,
                };
                write!(reason, ": {}", err).unwrap();
            }
            emit(reason, vec![(span, None)]);
            NFA::never_match()
        });

    if nfa.has_empty() {
        emit("Tokens must not match the empty string", vec![(span, None)]);
    }
    nfa
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NonTerminalDef {
    Goal {
        rule: Rule,
    },
    Named {
        name: Name,
        generics: Vec<NonTerminalDef>,
        span: Span,
    },
    Anonymous {
        rule: Rule,
    },
}

impl NonTerminalDef {
    pub fn span(&self) -> Span {
        match self {
            NonTerminalDef::Goal { rule, .. } => rule.span,
            &NonTerminalDef::Named { span, .. } => span,
            NonTerminalDef::Anonymous { rule, .. } => rule.span,
        }
    }
}

impl fmt::Display for NonTerminalDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NonTerminalDef::Goal { rule } => {
                write!(f, "Goal({rule})")?;
            }
            NonTerminalDef::Named {
                name,
                generics,
                span: _,
            } => {
                write!(f, "{name}")?;
                if !generics.is_empty() {
                    f.write_str("<")?;
                    for (i, generic) in generics.iter().enumerate() {
                        if i != 0 {
                            f.write_str(", ")?;
                        }
                        write!(f, "{generic}")?;
                    }
                    f.write_str(">")?;
                }
            }
            NonTerminalDef::Anonymous { rule } => {
                write!(f, "{{{rule}}}")?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NonTerminalUse {
    Goal {
        rule: Rule,
    },
    Named {
        name: Name,
        generics: Vec<NonTerminalUse>,
        span: Span,
    },
    Anonymous {
        rule: Rule,
        context: Option<Name>,
        generics: BTreeMap<Ident, NonTerminalUse>,
    },
}

impl NonTerminalUse {
    fn new_anonymous(rule: Rule, context: Option<&Name>, generics: BTreeMap<Ident, Self>) -> Self {
        fn contains_non_super_ident(rule: &Rule, context: &Ident) -> bool {
            rule.alternatives
                .iter()
                .flat_map(|expression| &expression.sequence)
                .any(|(item, _, _)| match item {
                    Item::Ident {
                        mark,
                        ident,
                        generics: _,
                    } => ident == context && mark != &Mark::Super,
                    Item::String(_) | Item::Regex(_) => false,
                    Item::Group(rule) => contains_non_super_ident(rule, context),
                    Item::Lookaround(_, rule) => contains_non_super_ident(rule, context),
                })
        }
        let context = context
            .filter(|name| contains_non_super_ident(&rule, &name.ident))
            .cloned();
        Self::Anonymous {
            rule,
            context,
            generics,
        }
    }

    pub fn definition(&self, language: &Language) -> NonTerminalDef {
        match self {
            NonTerminalUse::Goal { rule } => NonTerminalDef::Goal { rule: rule.clone() },
            NonTerminalUse::Named {
                name,
                generics,
                span: _,
            } => NonTerminalDef::Named {
                name: name.clone(),
                generics: generics
                    .iter()
                    .map(|generic| generic.definition(language))
                    .collect(),
                span: language.definitions[&name.ident].span,
            },
            NonTerminalUse::Anonymous {
                rule,
                context: _,
                generics: _,
            } => NonTerminalDef::Anonymous { rule: rule.clone() },
        }
    }

    pub fn span(&self) -> Span {
        match self {
            NonTerminalUse::Goal { rule, .. } => rule.span,
            NonTerminalUse::Named { span, .. } => *span,
            NonTerminalUse::Anonymous { rule, .. } => rule.span,
        }
    }
}

impl fmt::Display for NonTerminalUse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NonTerminalUse::Goal { rule } => {
                write!(f, "Goal({rule})")?;
            }
            NonTerminalUse::Named {
                name,
                generics,
                span: _,
            } => {
                write!(f, "{name}")?;
                if !generics.is_empty() {
                    f.write_str("<")?;
                    for (i, generic) in generics.iter().enumerate() {
                        if i != 0 {
                            f.write_str(", ")?;
                        }
                        write!(f, "{generic}")?;
                    }
                    f.write_str(">")?;
                }
            }
            NonTerminalUse::Anonymous {
                rule,
                generics,
                context,
            } => {
                match context {
                    Some(context) => write!(f, "{{{rule}}}#{context}")?,
                    None => write!(f, "{{{rule}}}")?,
                }
                if !generics.is_empty() {
                    f.write_str("<")?;
                    for (i, (name, value)) in generics.iter().enumerate() {
                        if i != 0 {
                            f.write_str(", ")?;
                        }
                        write!(f, "{name}={value}")?;
                    }
                    f.write_str(">")?;
                }
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name {
    pub ident: Ident,
    pub index: usize,
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.ident)?;
        if self.index > 0 {
            write!(f, "#{}", self.index)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum TerminalUse {
    Named {
        ident: Ident,
        span: Span,
    },
    Anonymous {
        name: Arc<str>,
        regex: NFA,
        span: Span,
    },
    EndOfInput {
        span: Span,
    },
}

impl TerminalUse {
    pub fn span(&self) -> Span {
        match *self {
            Self::Named { span, .. }
            | Self::Anonymous { span, .. }
            | Self::EndOfInput { span, .. } => span,
        }
    }

    pub fn definition(&self, language: &Language) -> TerminalDef {
        match self {
            Self::Named { ident, .. } => TerminalDef::Named {
                ident: ident.clone(),
                span: language.definitions[ident].span,
            },
            Self::Anonymous { name, regex, .. } => TerminalDef::Anonymous {
                name: name.clone(),
                regex: regex.clone(),
            },
            Self::EndOfInput { .. } => TerminalDef::EndOfInput,
        }
    }
}

impl fmt::Display for TerminalUse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TerminalUse::Named { ident, .. } => write!(f, "@{ident}"),
            TerminalUse::Anonymous { name, .. } => write!(f, "@'{name}'"),
            TerminalUse::EndOfInput { .. } => write!(f, "$"),
        }
    }
}

impl PartialEq for TerminalUse {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Named {
                    ident: this,
                    span: this_span,
                },
                Self::Named {
                    ident: other,
                    span: other_span,
                },
            ) => this == other && this_span == other_span,
            (
                Self::Anonymous {
                    name: this,
                    regex: _,
                    span: this_span,
                },
                Self::Anonymous {
                    name: other,
                    regex: _,
                    span: other_span,
                },
            ) => {
                // If we were being efficient we could probably only compare the spans
                this == other && this_span == other_span
            }
            (Self::EndOfInput { span: this }, Self::EndOfInput { span: other }) => this == other,
            _ => false,
        }
    }
}
impl Eq for TerminalUse {}
impl PartialOrd for TerminalUse {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TerminalUse {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (
                Self::Named {
                    ident: this,
                    span: this_span,
                },
                Self::Named {
                    ident: other,
                    span: other_span,
                },
            ) => this.cmp(other).then_with(|| this_span.cmp(other_span)),
            (
                Self::Anonymous {
                    name: this,
                    regex: _,
                    span: this_span,
                },
                Self::Anonymous {
                    name: other,
                    regex: _,
                    span: other_span,
                },
            ) => {
                // If we were being efficient we could probably only compare the spans
                this.cmp(other).then_with(|| this_span.cmp(other_span))
            }
            (Self::EndOfInput { span: this }, Self::EndOfInput { span: other }) => this.cmp(other),
            (Self::Named { .. }, _) => Ordering::Greater,
            (_, Self::Named { .. }) => Ordering::Less,
            (Self::Anonymous { .. }, _) => Ordering::Greater,
            (_, Self::Anonymous { .. }) => Ordering::Less,
        }
    }
}
impl Hash for TerminalUse {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            Self::Named { ident, span } => {
                ident.hash(state);
                span.hash(state);
            }
            Self::Anonymous {
                name,
                regex: _,
                span,
            } => {
                name.hash(state);
                span.hash(state);
            }
            Self::EndOfInput { span } => span.hash(state),
        }
    }
}

#[derive(Debug, Clone)]
pub enum TerminalDef {
    Named { ident: Ident, span: Span },
    Anonymous { name: Arc<str>, regex: NFA },
    EndOfInput,
}

impl TerminalDef {
    pub fn name(&self) -> &str {
        match self {
            Self::Named { ident, .. } => &ident.0,
            Self::Anonymous { name, .. } => name,
            Self::EndOfInput => "$",
        }
    }

    pub fn ident(&self) -> Option<&Ident> {
        match self {
            Self::Named { ident, .. } => Some(ident),
            Self::Anonymous { .. } | Self::EndOfInput { .. } => None,
        }
    }
}

impl fmt::Display for TerminalDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TerminalDef::Named { ident, .. } => write!(f, "@{ident}"),
            TerminalDef::Anonymous { name, .. } => write!(f, "@'{name}'"),
            TerminalDef::EndOfInput => write!(f, "$"),
        }
    }
}
impl PartialEq for TerminalDef {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Named {
                    ident: this_name,
                    span: this_span,
                },
                Self::Named {
                    ident: other_name,
                    span: other_span,
                },
            ) => this_name == other_name && this_span == other_span,
            (
                Self::Anonymous {
                    name: this,
                    regex: _,
                },
                Self::Anonymous {
                    name: other,
                    regex: _,
                },
            ) => this == other,
            (Self::EndOfInput, Self::EndOfInput) => true,
            _ => false,
        }
    }
}
impl Eq for TerminalDef {}
impl PartialOrd for TerminalDef {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TerminalDef {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (
                Self::Named {
                    ident: this_name,
                    span: this_span,
                },
                Self::Named {
                    ident: other_name,
                    span: other_span,
                },
            ) => this_name
                .cmp(other_name)
                .then_with(|| this_span.cmp(other_span)),
            (
                Self::Anonymous {
                    name: this,
                    regex: _,
                },
                Self::Anonymous {
                    name: other,
                    regex: _,
                },
            ) => this.cmp(other),
            (Self::EndOfInput, Self::EndOfInput) => Ordering::Equal,
            (Self::Named { .. }, _) => Ordering::Greater,
            (_, Self::Named { .. }) => Ordering::Less,
            (Self::Anonymous { .. }, _) => Ordering::Greater,
            (_, Self::Anonymous { .. }) => Ordering::Less,
        }
    }
}
impl Hash for TerminalDef {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            Self::Named { ident, span } => {
                ident.hash(state);
                span.hash(state);
            }
            Self::Anonymous { name, regex: _ } => {
                name.hash(state);
            }
            Self::EndOfInput => {}
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Production {
    pub alternatives: Vec<Alternative>,
}

impl fmt::Display for Production {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, alternative) in self.alternatives.iter().enumerate() {
            if i != 0 {
                write!(f, " | ")?;
            }
            write!(f, "{alternative}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Alternative {
    pub span: Span,
    pub terms: Vec<Term>,
    pub negative_lookahead: Option<NonTerminalUse>,
}

impl fmt::Display for Alternative {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, term) in self.terms.iter().enumerate() {
            if i != 0 {
                write!(f, " ")?;
            }
            write!(f, "{term}")?;
        }
        if let Some(non_terminal) = &self.negative_lookahead {
            write!(f, " (!>>{non_terminal})")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Term {
    pub kind: TermKind,
    pub silent: bool,
}

impl Term {
    pub fn span(&self) -> Span {
        match &self.kind {
            TermKind::Terminal(terminal) => terminal.span(),
            TermKind::NonTerminal(non_terminal) => non_terminal.span(),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.silent {
            f.write_char('-')?;
        }
        <TermKind as fmt::Display>::fmt(&self.kind, f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TermKind {
    Terminal(TerminalUse),
    NonTerminal(NonTerminalUse),
}

impl fmt::Display for TermKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermKind::Terminal(terminal) => write!(f, "{terminal}"),
            TermKind::NonTerminal(non_terminal) => write!(f, "{non_terminal}"),
        }
    }
}
