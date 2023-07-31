use regex_automata::{nfa::thompson::pikevm::PikeVM, Anchored, Input};
use tracing::instrument;

use crate::{
    language::{Ident, ParseTree, Test},
    lower::{Name, NonTerminal, Term, Terminal},
    parse_table::{Action, LrkParseTable},
};

#[instrument]
pub fn run_test(parse_table: &LrkParseTable, test: &Test) -> Option<ParseTree> {
    let mut states = vec![parse_table.start_states[&test.ident]];
    let mut forest = vec![];
    let input = Input::new(&*test.test).anchored(Anchored::Yes);
    let mut offset = 0;
    let tree = loop {
        let state = &parse_table[*states.last().unwrap()];
        let action = {
            let mut action = &state.action;
            let mut lookahead = 0;
            loop {
                let Action::Ambiguous {
                    nfa,
                    regexes: _,
                    actions,
                    eoi,
                } = action
                else {
                    break;
                };
                if input.get_span().len() == offset + lookahead {
                    action = &eoi[&test.ident];
                    break;
                } else {
                    let pike_vm = PikeVM::new_from_nfa(nfa.clone()).unwrap();
                    let half_match = pike_vm
                        .find(
                            &mut pike_vm.create_cache(),
                            input.clone().range((offset + lookahead)..),
                        )
                        .expect("No matches");
                    action = &actions[half_match.pattern().as_usize()];
                    lookahead += half_match.len();
                }
            }
            action
        };
        match action {
            Action::Ambiguous { .. } => unreachable!(),
            Action::Shift(Terminal::Token(nfa, _), new_state) => {
                let pike_vm = PikeVM::new_from_nfa(nfa.clone()).unwrap();
                let half_match = pike_vm
                    .find(&mut pike_vm.create_cache(), input.clone().range(offset..))
                    .expect("No matches");
                forest.push(ParseTree::Leaf {
                    ident: None,
                    data: String::from_utf8(input.haystack()[half_match.range()].to_owned())
                        .unwrap(),
                });
                states.push(*new_state);
                offset = half_match.end();
            }
            Action::Shift(Terminal::EndOfInput(_), new_state) => {
                forest.push(ParseTree::Leaf {
                    ident: None,
                    data: String::new(),
                });
                states.push(*new_state);
            }
            Action::Reduce(non_terminal, alternative) => {
                let nodes =
                    forest.split_off(forest.len().checked_sub(alternative.terms.len()).unwrap());
                states.truncate(states.len().checked_sub(alternative.terms.len()).unwrap());
                let ident = match non_terminal {
                    NonTerminal::Goal { .. } => {
                        if alternative.terms[0].atomic {
                            break ParseTree::Leaf {
                                ident: nodes[0].ident().cloned(),
                                data: nodes[0].data(),
                            };
                        } else {
                            break nodes.into_iter().next().unwrap();
                        }
                    }
                    NonTerminal::Named {
                        name: Name { ident, .. },
                    } => ident.clone(),
                    NonTerminal::Anonymous { .. } => Ident("anon".into()),
                };

                let nodes = nodes
                    .into_iter()
                    .zip(&alternative.terms)
                    .flat_map(|(node, term)| match term {
                        Term {
                            kind: _,
                            silent: true,
                            atomic: true,
                        } => vec![],
                        Term {
                            kind: _,
                            silent: true,
                            atomic: false,
                        } => match node {
                            ParseTree::Leaf { .. } => vec![],
                            ParseTree::Node { nodes, .. } => nodes,
                        },
                        Term {
                            kind: _,
                            silent: false,
                            atomic: true,
                        } => vec![ParseTree::Leaf {
                            ident: node.ident().cloned(),
                            data: node.data(),
                        }],
                        Term {
                            kind: _,
                            silent: false,
                            atomic: false,
                        } => vec![node],
                    })
                    .collect();

                forest.push(ParseTree::Node { ident, nodes });
                let state = &parse_table[*states.last().unwrap()];
                states.push(state.goto[non_terminal]);
            }
        }
    };
    if tree == test.parse_tree {
        None
    } else {
        Some(tree)
    }
}
