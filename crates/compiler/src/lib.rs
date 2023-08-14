pub mod diagnostics;
pub mod language;
pub mod lower;
pub mod parse_table;
pub mod test;
pub mod util;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}
