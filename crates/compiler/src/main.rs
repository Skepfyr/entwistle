use std::{collections::HashSet, convert::TryInto, error::Error};

use entwistle::{
    language::Language,
    lower::{
        Lower, Name, NonTerminal, NonTerminalData, ResolvedTerm, Term, Terminal, TerminalData,
    },
    parse_table::{ConflictedAction, LrkParseTable, ParseTable},
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
    let ident = db.intern_ident(std::env::args().nth(2).unwrap());
    let non_terminal = match db.term(ident) {
        Term::NonTerminal(nt) => nt,
        _ => panic!(),
    };

    let mut visited = HashSet::new();
    let mut to_print = vec![non_terminal];
    visited.insert(non_terminal);

    while let Some(nt) = to_print.pop() {
        let production = db.production(nt);
        print_nt(&db, nt);
        print!(" -> ");
        for (i, alt) in production.into_iter().enumerate() {
            if i != 0 {
                print!("| ");
            }
            if alt.is_empty() {
                print!("() ");
            }
            for &term in &*alt {
                match term {
                    Term::NonTerminal(next_nt) => {
                        if !visited.contains(&next_nt) {
                            to_print.push(next_nt);
                            visited.insert(next_nt);
                        }
                        print_nt(&db, next_nt);
                    }
                    Term::Terminal(term) => print_terminal(&db, term),
                    Term::This => print_nt(&db, nt),
                }
                print!(" ")
            }
        }
        println!();
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

    let lr0_parse_table = db.lr0_parse_table(non_terminal);
    println!("Start state: {}", lr0_parse_table.start_state);
    for (i, state) in lr0_parse_table.states.iter().enumerate() {
        println!("State {}:", i);
        println!("  Items:");
        for (item, _backlinks) in &state.item_set {
            print!("    ");
            print_nt(&db, item.non_terminal);
            print!(" ->");
            for term in &item.production[..item.index] {
                print!(" ");
                match term.resolve_this(item.non_terminal) {
                    ResolvedTerm::Terminal(t) => print_terminal(&db, t),
                    ResolvedTerm::NonTerminal(nt) => print_nt(&db, nt),
                }
            }
            print!(" .");
            for term in &item.production[item.index..] {
                print!(" ");
                match term.resolve_this(item.non_terminal) {
                    ResolvedTerm::Terminal(t) => print_terminal(&db, t),
                    ResolvedTerm::NonTerminal(nt) => print_nt(&db, nt),
                }
            }
            println!();
        }
        println!("  Actions:");
        for (&t, &state) in &state.actions {
            print!("    ");
            print_terminal(&db, t);
            println!(" -> {}", state);
        }
        for (&nt, &state) in &state.goto {
            print!("    ");
            print_nt(&db, nt);
            println!(" -> {}", state);
        }
    }

    println!("--------------");

    for (source_state, conflicts) in &*db.lane_table(non_terminal) {
        println!("Source state {}:", source_state);
        for ((state, conflict), disambiguators) in conflicts {
            print!("  State {}: ", state);
            match *conflict {
                ConflictedAction::Shift(terminal) => {
                    print!("Shift(");
                    print_terminal(&db, terminal);
                    println!(")")
                }
                ConflictedAction::Reduce(nt, ref terms) => {
                    print!("Reduce(");
                    print_nt(&db, nt);
                    print!(" ->");
                    for term in &**terms {
                        print!(" ");
                        match term.resolve_this(nt) {
                            ResolvedTerm::Terminal(t) => print_terminal(&db, t),
                            ResolvedTerm::NonTerminal(nt) => print_nt(&db, nt),
                        }
                    }
                    println!(")")
                }
            }
            for disambiguator in disambiguators {
                print!("   ");
                for &terminal in disambiguator {
                    print!(" ");
                    print_terminal(&db, terminal);
                }
                println!();
            }
        }
    }

    println!("--------------");

    Ok(())
}

fn print_nt(db: &EntwistleDatabase, nt: NonTerminal) {
    match db.lookup_intern_non_terminal(nt) {
        NonTerminalData::Goal { non_terminal } => {
            print!("Goal(");
            print_nt(db, non_terminal);
            print!(")");
        }
        NonTerminalData::Named { name, scope } => {
            print!("{}#{}{{", db.lookup_intern_ident(name.ident), name.index,);
            for (key, Name { ident, index }) in scope.ident_map {
                print!(
                    "{}: {}#{}, ",
                    db.lookup_intern_ident(key),
                    db.lookup_intern_ident(ident),
                    index
                )
            }
            print!("}}");
        }
        NonTerminalData::Anonymous { .. } => print!("#{}", nt.0),
    }
}

fn print_terminal(db: &EntwistleDatabase, term: Terminal) {
    match db.lookup_intern_terminal(term) {
        TerminalData::Real { name, data } => {
            if let Some(name) = name {
                print!("{}#{}(", db.lookup_intern_ident(name), term.0);
            } else {
                print!("#{}(", term.0);
            }
            print!("{:?})", data);
        }
        TerminalData::EndOfInput => print!("EoI"),
    }
}
