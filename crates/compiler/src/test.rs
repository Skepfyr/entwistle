use std::fmt::Write;

use regex_automata::{nfa::thompson::pikevm::PikeVM, Anchored, Input};
use tracing::instrument;

use crate::{
    diagnostics::emit,
    language::{Language, ParseTree, Test},
    lower::{terminal_nfa, Term},
    parse_table::{parse_table, Action, StateId},
    util::DisplayWithDb,
    Db,
};

#[instrument(skip_all)]
#[salsa::tracked]
pub fn run_test(db: &dyn Db, language: Language, test: Test) -> Option<Vec<ParseTree>> {
    let parse_table = parse_table(db, language, test.goal(db).clone());
    let mut states = vec![StateId::START];
    let mut forest = vec![];
    let input = Input::new(test.test(db)).anchored(Anchored::Yes);
    let mut offset = 0;
    let trees = loop {
        let state = &parse_table[*states.last().unwrap()];
        let action = {
            let mut action = &state.action;
            let mut lookahead = 0;
            loop {
                let Action::Ambiguous {
                    nfa,
                    terminals,
                    actions,
                } = action
                else {
                    break;
                };
                let pike_vm = PikeVM::new_from_nfa(nfa.clone()).unwrap();
                let Some(half_match) = pike_vm.find(
                    &mut pike_vm.create_cache(),
                    input.clone().range((offset + lookahead)..),
                ) else {
                    let mut message = "Expected one of: ".to_string();
                    for (i, terminal) in terminals.iter().enumerate() {
                        if i != 0 {
                            write!(message, ", ").unwrap();
                        }
                        write!(message, "{}", terminal.display(db)).unwrap();
                    }
                    emit(
                        "Unable to find a match for any expected token",
                        vec![(
                            crate::Span {
                                start: test.test_span(db).start + offset,
                                end: test.test_span(db).start + offset,
                            },
                            Some(message),
                        )],
                    );
                    return None;
                };
                action = &actions[half_match.pattern().as_usize()];
                lookahead += half_match.len();
            }
            action
        };
        match action {
            Action::Ambiguous { .. } => unreachable!(),
            Action::Shift(terminal, new_state) => {
                let regex = terminal_nfa(db, language, terminal);
                let pike_vm = PikeVM::new_from_nfa(regex).unwrap();
                let Some(half_match) =
                    pike_vm.find(&mut pike_vm.create_cache(), input.clone().range(offset..))
                else {
                    emit(
                        format!("Expected token: {}", terminal.name(db)),
                        vec![(
                            crate::Span {
                                start: test.test_span(db).start + offset,
                                end: test.test_span(db).start + offset,
                            },
                            None,
                        )],
                    );
                    return None;
                };
                forest.push(ParseTree::Leaf {
                    ident: terminal.ident().cloned(),
                    data: String::from_utf8(input.haystack()[half_match.range()].to_owned())
                        .unwrap(),
                });
                states.push(*new_state);
                offset = half_match.end();
            }
            Action::Reduce(non_terminal, alternative) => {
                let nodes = forest.split_off(
                    forest
                        .len()
                        .checked_sub(alternative.terms(db).len())
                        .unwrap(),
                );
                states.truncate(
                    states
                        .len()
                        .checked_sub(alternative.terms(db).len())
                        .unwrap(),
                );
                let ident = non_terminal.ident(db);

                let nodes: Vec<_> = nodes
                    .into_iter()
                    .zip(alternative.terms(db))
                    .flat_map(|(node, term)| match term {
                        Term {
                            kind: _,
                            silent: true,
                        } => match node {
                            ParseTree::Leaf { ident: _, data } => {
                                vec![ParseTree::Leaf { ident: None, data }]
                            }
                            ParseTree::Node { ident: _, nodes } => nodes,
                        },
                        Term {
                            kind: _,
                            silent: false,
                        } => vec![node],
                    })
                    .collect();

                if non_terminal.is_goal(db) {
                    let mut nodes = nodes;
                    let eoi = nodes.pop().expect("Goal node must have EOI");
                    assert!(
                        matches!(eoi, ParseTree::Leaf { ident: None, data } if data.is_empty())
                    );
                    break nodes;
                }

                forest.push(ParseTree::Node { ident, nodes });
                let state = &parse_table[*states.last().unwrap()];
                states.push(state.goto[non_terminal]);
            }
        }
    };
    if &trees == test.parse_trees(db) {
        None
    } else {
        Some(trees)
    }
}
