use parking_lot::Mutex;

use crate::Span;

static DIAGNOSTICS: Mutex<Vec<Diagnostic>> = Mutex::new(Vec::new());

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Diagnostic {
    pub span: Span,
    pub message: String,
}

