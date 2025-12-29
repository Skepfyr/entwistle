use std::fmt;

pub(crate) use salsa::Database as Db;

pub mod diagnostics;
pub mod language;
pub mod lower;
pub mod parse_table;
pub mod test;

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

#[salsa::db]
#[derive(Default, Clone)]
pub struct Database {
    storage: salsa::Storage<Self>,
}

#[salsa::db]
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
