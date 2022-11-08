use std::{collections::HashSet, convert::TryInto, error::Error};

use entwistle::{
    language::Language,
    lower::{Lower, NonTerminalData, Term},
    parse_table::ParseTable,
    util::DbDisplay,
    EntwistleDatabase,
};
use tracing::Level;
use tracing_subscriber::{filter, prelude::*};

fn main() -> Result<(), Box<dyn Error>> {
    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer().pretty())
        .with(filter::Targets::new().with_target("entwistle", Level::TRACE))
        .init();
    let file = std::env::args().nth(1).unwrap();

    let db = EntwistleDatabase::oneshot(file.try_into().unwrap());

    let mut visited = HashSet::new();
    let mut to_print: Vec<_> = db
        .idents()
        .iter()
        .filter_map(|&ident| match db.term(ident) {
            Term::Terminal(_) => None,
            Term::NonTerminal(nt) => Some(nt),
        })
        .collect();
    visited.extend(to_print.iter().copied());

    while let Some(nt) = to_print.pop() {
        let production = db.production(nt);
        println!("{}", production.display(&db));
        for terms in production {
            for term in &*terms {
                if let &Term::NonTerminal(next_nt) = term {
                    if !visited.contains(&next_nt) {
                        to_print.push(next_nt);
                        visited.insert(next_nt);
                    }
                }
            }
        }
    }

    println!("--------------");

    for ident in visited
        .into_iter()
        .flat_map(|nt| {
            if let NonTerminalData::Named { name, .. } = db.lookup_intern_non_terminal(nt) {
                Some(name.ident)
            } else {
                None
            }
        })
        .collect::<HashSet<_>>()
    {
        let deps = db.direct_dependencies(ident);
        print!("{}: ", db.lookup_intern_ident(ident));
        for (i, dep) in deps.into_iter().enumerate() {
            if i > 0 {
                print!(", ");
            }
            print!("{}", db.lookup_intern_ident(dep));
        }
        println!()
    }

    println!("--------------");

    println!("{}", db.lr0_parse_table().display(&db));

    println!("--------------");

    println!("{}", db.parse_table().display(&db));

    println!("--------------");

    Ok(())
}
