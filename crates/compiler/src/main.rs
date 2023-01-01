use std::error::Error;

use entwistle::{language::Language, lower::lower, parse_table::parse_table, test::run_test};
use tracing::Level;
use tracing_subscriber::{filter, prelude::*};

fn main() -> Result<(), Box<dyn Error>> {
    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer().pretty())
        .with(filter::Targets::new().with_target("entwistle", Level::TRACE))
        .init();
    let file = std::env::args().nth(1).unwrap();

    let input = std::fs::read_to_string(file)?;
    let language = Language::parse(&input);

    println!("{language:?}");
    println!("--------------");

    let grammar = lower(&language);

    println!("{grammar}");
    println!("--------------");

    let parse_table = parse_table(&grammar);
    println!("{parse_table}");

    println!("--------------");

    for test in language.tests.values().flatten() {
        if let Some(tree) = run_test(&parse_table, test) {
            println!("Test failed:\n{tree}");
        }
    }

    Ok(())
}
