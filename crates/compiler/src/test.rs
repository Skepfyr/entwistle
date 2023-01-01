use tracing::instrument;

use crate::{
    language::{Ident, ParseTree, Test},
    lower::{Name, NonTerminal, Terminal},
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
    loop {
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
                match terminal {
                    &Terminal::Real(data) => {
                        forest.push(ParseTree::Leaf { data });
                        states.push(*new_state);
                    }
                    _ => break,
                }
            }
            Action::Reduce(non_terminal, terms) => {
                let nodes = forest.split_off(forest.len().checked_sub(terms.len()).unwrap());
                states.truncate(states.len().checked_sub(terms.len()).unwrap());
                let ident = match non_terminal {
                    NonTerminal::Goal { .. } => unreachable!(),
                    NonTerminal::Named {
                        name: Name { ident, .. },
                    } => ident.clone(),
                    NonTerminal::Anonymous { index } => Ident(format!("#{index}").into()),
                };
                forest.push(ParseTree::Node { ident, nodes });
                let state = &parse_table[*states.last().unwrap()];
                states.push(state.goto[non_terminal]);
            }
        }
    }
    assert!(forest.len() == 1);
    let tree = forest.into_iter().next().unwrap();
    if tree == test.parse_tree {
        None
    } else {
        Some(tree)
    }
}
