use regex_automata::dfa::Automaton;
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
    let mut input: &str = &test.test;
    let tree = loop {
        let state = &parse_table[*states.last().unwrap()];
        let action = {
            let mut action = &state.action;
            let mut lookahead = 0;
            loop {
                let Action::Ambiguous { dfa, regexes: _, actions, eoi } = action else { break };
                if input.len() == lookahead {
                    action = &eoi[&test.ident];
                    break;
                } else {
                    let half_match = dfa
                        .find_leftmost_fwd(input[lookahead..].as_bytes())
                        .unwrap()
                        .expect("No matches");
                    action = &actions[half_match.pattern().as_usize()];
                    lookahead += half_match.offset();
                }
            }
            action
        };
        match action {
            Action::Ambiguous { .. } => unreachable!(),
            Action::Shift(Terminal::Token(dfa, _), new_state) => {
                let half_match = dfa
                    .find_leftmost_fwd(input.as_bytes())
                    .unwrap()
                    .expect("No matches");
                forest.push(ParseTree::Leaf {
                    ident: None,
                    data: input[..half_match.offset()].to_owned(),
                });
                states.push(*new_state);
                input = &input[half_match.offset()..];
            }
            Action::Shift(Terminal::EndOfInput(_), new_state) => {
                forest.push(ParseTree::Leaf {
                    ident: None,
                    data: String::new(),
                });
                states.push(*new_state);
            }
            Action::Reduce(non_terminal, terms) => {
                let nodes = forest.split_off(forest.len().checked_sub(terms.len()).unwrap());
                states.truncate(states.len().checked_sub(terms.len()).unwrap());
                let ident = match non_terminal {
                    NonTerminal::Goal { .. } => {
                        if terms[0].atomic {
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
                    NonTerminal::Anonymous { index } => Ident(format!("#{index}").into()),
                };

                let nodes = nodes
                    .into_iter()
                    .zip(terms)
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
