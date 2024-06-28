use std::{
    collections::{BTreeSet, HashSet},
    path::Path,
};

use color_eyre::Result;
use entwistle::{
    debug_new_non_terminal,
    diagnostics::diagnostics,
    language::{self, Expression, Rule, Source},
    lower::{Term, TermKind},
    parse_table::{lr0_parse_table, parse_table, term_string::TermString},
    test::run_test,
    util::DisplayWithDb,
    Database, Span,
};
use tracing_subscriber::prelude::*;

fn main() -> Result<()> {
    color_eyre::install()?;
    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer().pretty())
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_error::ErrorLayer::default())
        .init();

    let db = Database::default();

    let file = std::env::args().nth(1).unwrap();
    let file = Path::new(&file);

    let input = Source::new(&db, std::fs::read_to_string(file)?);
    let language = language::parse(&db, input);

    let diags = diagnostics();
    if !diags.is_empty() {
        for diag in diags {
            diag.print(input.text(&db), file).unwrap();
        }
        return Ok(());
    }

    println!("--------------");

    // let inner_item = *language
    //     .definitions(&db)
    //     .keys()
    //     .find(|ident| ident.name(&db) == "ExpressionWithoutBlock")
    //     .unwrap();
    // let used_items = language.dependencies(&db, inner_item, Span { start: 0, end: 0 });
    // let mut unused_items = language
    //     .definitions(&db)
    //     .keys()
    //     .copied()
    //     .filter(|item| *item != inner_item && !used_items.contains(item))
    //     .map(|item| item.name(&db))
    //     .collect::<Vec<_>>();
    // unused_items.sort_unstable();
    // for unused_item in unused_items {
    //     println!("Unused item: {}", unused_item);
    // }

    // let pattern = *language
    //     .definitions(&db)
    //     .keys()
    //     .find(|ident| ident.name(&db) == "Pattern")
    //     .unwrap();
    // let pattern = debug_new_non_terminal(&db, pattern);
    // let mut visited = HashSet::new();
    // let mut to_add = VecDeque::new();
    // to_add.push_back(NormalNonTerminal::Original(pattern));
    // while let Some(nt) = to_add.pop_front() {
    //     if visited.insert(nt.clone()) {
    //         let production = normal_production(&db, language, &nt);
    //         println!("{}:", nt.display(&db));
    //         for alternative in production {
    //             print!("  ");
    //             for term in alternative {
    //                 if let NormalTerm::NonTerminal(nt) = &term {
    //                     to_add.push_back(nt.clone());
    //                 }
    //                 print!("{} ", term.display(&db));
    //             }
    //             println!();
    //         }
    //     }
    // }

    // let mut non_terminals = language
    //     .definitions(&db)
    //     .iter()
    //     .filter(|(_, definition)| definition.generics.is_empty() && !definition.atomic)
    //     .map(|(ident, definition)| {
    //         NonTerminalUse::new_goal(
    //             &db,
    //             Rule {
    //                 span: definition.span,
    //                 alternatives: {
    //                     let mut alternatives = BTreeSet::new();
    //                     alternatives.insert(Expression {
    //                         span: definition.span,
    //                         sequence: vec![(
    //                             Item::Ident {
    //                                 mark: Mark::This,
    //                                 ident: *ident,
    //                                 generics: Vec::new(),
    //                             },
    //                             Quantifier::Once,
    //                             definition.span,
    //                         )],
    //                     });
    //                     alternatives
    //                 },
    //             },
    //         )
    //     })
    //     .collect::<Vec<_>>();
    // let mut visited = HashSet::new();
    // while let Some(non_terminal) = non_terminals.pop() {
    //     let production = production(&db, language, non_terminal);
    //     println!("{}: {}", non_terminal.display(&db), production.display(&db));
    //     production
    //         .alternatives
    //         .iter()
    //         .flat_map(|expression| {
    //             expression
    //                 .terms
    //                 .iter()
    //                 .filter_map(|term| match term.kind {
    //                     TermKind::Terminal(_) => None,
    //                     TermKind::NonTerminal(nt) => Some(nt),
    //                 })
    //                 .chain(expression.negative_lookahead)
    //         })
    //         .for_each(|nt| {
    //             if visited.insert(nt) {
    //                 non_terminals.push(nt);
    //             }
    //         });
    // }

    // let diags = diagnostics();
    // if !diags.is_empty() {
    //     for diag in diags {
    //         diag.print(input.text(&db), file).unwrap();
    //     }
    //     return Ok(());
    // }
    // let parse_table = parse_table(&db, language, language.tests(&db)[0].goal(&db).clone());
    // println!("{}", parse_table.display(&db));

    println!("--------------");

    for &test in language.tests(&db) {
        if let Some(trees) = run_test(&db, language, test) {
            println!("Test failed:");
            for tree in trees {
                println!("{}", tree.display(&db));
            }
        }

        let diags = diagnostics();
        if !diags.is_empty() {
            for diag in diags {
                diag.print(input.text(&db), file).unwrap();
            }
            return Ok(());
        }
    }

    Ok(())
}
