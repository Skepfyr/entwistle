use std::fmt;

pub mod diagnostics;
pub mod language;
pub mod lower;
pub mod parse_table;
pub mod test;
pub mod util;

#[salsa::jar(db = Db)]
pub struct Jar(
    language::Ident,
    language::Source,
    language::parse,
    language::Language,
    language::Language_definition,
    language::Language_dependencies,
    language::Language_direct_dependencies,
    language::Test,
    lower::production,
    lower::NonTerminal,
    lower::Production,
    lower::Alternative,
    parse_table::term_string::normal_production,
    parse_table::term_string::can_production_be_empty,
    test::run_test,
    debug_new_non_terminal,
);

#[salsa::tracked]
pub fn debug_new_non_terminal(db: &dyn Db, ident: language::Ident) -> lower::NonTerminal {
    lower::NonTerminal::new_named(
        db,
        lower::Name { ident, index: 0 },
        Vec::new(),
        crate::Span { start: 0, end: 0 },
    )
}

pub trait Db: salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: salsa::DbWithJar<Jar> {}

#[derive(Default)]
#[salsa::db(crate::Jar)]
pub struct Database {
    storage: salsa::Storage<Self>,
}

impl salsa::Database for Database {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}
