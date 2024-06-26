use std::fmt;

pub mod diagnostics;
pub mod language;
pub mod lower;
pub mod parse_table;
pub mod test;
pub mod util;

#[salsa::jar(db = Db)]
pub struct Jar(
    language::Ident<'_>,
    language::Source,
    language::parse,
    language::Language<'_>,
    language::Language_definition,
    language::Language_dependencies,
    language::Language_direct_dependencies,
    language::Test<'_>,
    lower::production,
    lower::terminal_nfa,
    lower::NonTerminal<'_>,
    lower::NonTerminal_is_infinite,
    lower::Production<'_>,
    lower::Alternative<'_>,
    parse_table::lr0_parse_table,
    parse_table::terminals_conflict,
    test::run_test,
    debug_new_non_terminal,
);

#[salsa::tracked]
pub fn debug_new_non_terminal<'db>(
    db: &'db dyn Db,
    ident: language::Ident<'db>,
) -> lower::NonTerminal<'db> {
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
