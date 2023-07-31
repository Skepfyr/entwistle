use std::{collections::HashSet, error::Error};

use entwistle::{
    language::Language,
    lower::{production, NonTerminal, TermKind},
    parse_table::parse_table,
    test::run_test,
};
use tracing_subscriber::prelude::*;

fn main() -> Result<(), Box<dyn Error>> {
    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer().pretty())
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    let file = std::env::args().nth(1).unwrap();

    let input = std::fs::read_to_string(file)?;
    let language = Language::parse(&input);

    println!("--------------");

    let mut non_terminals = language
        .definitions
        .keys()
        .map(|ident| NonTerminal::Goal {
            ident: ident.clone(),
        })
        .collect::<Vec<_>>();
    let mut visited = HashSet::new();
    while let Some(non_terminal) = non_terminals.pop() {
        let production = production(&language, &non_terminal);
        println!("{non_terminal}: {production}");
        production
            .alternatives
            .iter()
            .flat_map(|expression| {
                expression
                    .terms
                    .iter()
                    .filter_map(|term| match &term.kind {
                        TermKind::Terminal(_) => None,
                        TermKind::NonTerminal(nt) => Some(nt),
                    })
                    .chain(expression.negative_lookahead.as_ref())
            })
            .for_each(|nt| {
                if visited.insert(nt.clone()) {
                    non_terminals.push(nt.clone());
                }
            });
    }

    println!("--------------");

    let parse_table = parse_table(&language);
    println!("{parse_table}");

    println!("--------------");

    for test in language.tests.values().flatten() {
        if let Some(tree) = run_test(&parse_table, test) {
            println!("Test failed:\n{tree}");
        }
    }

    Ok(())
}
