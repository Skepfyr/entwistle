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
    let input = test
        .test
        .chars()
        .map(Terminal::Real)
        .chain(std::iter::once(Terminal::EndOfInput(test.ident.clone())))
        .collect::<Vec<_>>();
    let mut i = 0;
    let tree = loop {
        let state = &parse_table[*states.last().unwrap()];
        let action = {
            let mut action = &state.action;
            let mut lookahead = i;
            loop {
                let Action::Ambiguous(ambiguities) = action else { break };
                action = &ambiguities[&input[lookahead]];
                lookahead += 1;
            }
            action
        };
        match action {
            Action::Ambiguous(_) => unreachable!(),
            Action::Shift(_terminal, new_state) => {
                let terminal = &input[i];
                i += 1;
                assert_eq!(terminal, _terminal);
                forest.push(ParseTree::Leaf {
                    ident: None,
                    data: match terminal {
                        Terminal::Real(data) => String::from(*data),
                        Terminal::EndOfInput(_) => String::new(),
                    },
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
