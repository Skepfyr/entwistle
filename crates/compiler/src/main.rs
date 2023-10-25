use std::{
    collections::{BTreeSet, HashSet},
    error::Error,
    path::Path,
};

use entwistle::{
    diagnostics::diagnostics,
    language::{Expression, Item, Language, Mark, Quantifier, Rule},
    lower::{production, NonTerminalUse, TermKind},
    test::run_test,
};
use tracing_subscriber::prelude::*;

fn main() -> Result<(), Box<dyn Error>> {
    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer().pretty())
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    let file = std::env::args().nth(1).unwrap();
    let file = Path::new(&file);

    let input = std::fs::read_to_string(file)?;
    let language = Language::parse(&input);

    let diags = diagnostics();
    if !diags.is_empty() {
        for diag in diags {
            diag.print(&input, file).unwrap();
        }
        return Ok(());
    }

    println!("--------------");

    let mut non_terminals = language
        .definitions
        .iter()
        .filter(|(_, definition)| definition.generics.is_empty() && !definition.atomic)
        .map(|(ident, definition)| NonTerminalUse::Goal {
            rule: Rule {
                span: definition.span,
                alternatives: {
                    let mut alternatives = BTreeSet::new();
                    alternatives.insert(Expression {
                        span: definition.span,
                        sequence: vec![(
                            Item::Ident {
                                mark: Mark::This,
                                ident: ident.clone(),
                                generics: Vec::new(),
                            },
                            Quantifier::Once,
                            definition.span,
                        )],
                    });
                    alternatives
                },
            },
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

    let diags = diagnostics();
    if !diags.is_empty() {
        for diag in diags {
            diag.print(&input, file).unwrap();
        }
        return Ok(());
    }

    println!("--------------");

    for test in &language.tests {
        if let Some(trees) = run_test(&language, test) {
            println!("Test failed:");
            for tree in trees {
                println!("{}", tree);
            }
        }

        let diags = diagnostics();
        if !diags.is_empty() {
            for diag in diags {
                diag.print(&input, file).unwrap();
            }
            return Ok(());
        }
    }

    Ok(())
}
