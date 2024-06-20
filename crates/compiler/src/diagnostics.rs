use std::{collections::HashSet, path::Path};

use ariadne::{Label, Report, ReportKind, Source};
use once_cell::sync::Lazy;
use parking_lot::Mutex;
use tracing::debug;

use crate::Span;

static DIAGNOSTICS: Lazy<Mutex<HashSet<Diagnostic>>> = Lazy::new(|| Mutex::new(HashSet::new()));

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Diagnostic {
    pub message: String,
    pub labels: Vec<(Span, Option<String>)>,
}

impl Diagnostic {
    pub fn print(&self, input: &str, path: &Path) -> std::io::Result<()> {
        let mut builder = Report::build(ReportKind::Error, (), self.labels[0].0.start)
            .with_message(&self.message);
        for (span, message) in &self.labels {
            let mut label = Label::new(*span);
            if let Some(message) = message {
                label = label.with_message(message);
            }
            builder.add_label(label);
        }
        builder
            .finish()
            .eprint(NamedSource(path, Source::from(input)))
    }
}

impl ariadne::Span for Span {
    type SourceId = ();

    fn source(&self) -> &Self::SourceId {
        &()
    }

    fn start(&self) -> usize {
        self.start
    }

    fn end(&self) -> usize {
        self.end
    }
}

struct NamedSource<'a>(&'a Path, Source<&'a str>);

impl<'a> ariadne::Cache<()> for NamedSource<'a> {
    type Storage = &'a str;

    fn fetch(&mut self, _: &()) -> Result<&Source<&'a str>, Box<dyn std::fmt::Debug + '_>> {
        Ok(&self.1)
    }

    fn display<'b>(&self, _: &'b ()) -> Option<Box<dyn std::fmt::Display + 'b>> {
        Some(Box::new(self.0.display().to_string()))
    }
}

pub fn emit(message: impl Into<String>, labels: Vec<(Span, Option<String>)>) {
    assert!(!labels.is_empty());
    emit_diagnostic(Diagnostic {
        message: message.into(),
        labels,
    });
}

pub fn emit_diagnostic(diagnostic: Diagnostic) {
    debug!("emitting diagnostic: {:?}", diagnostic);
    DIAGNOSTICS.lock().insert(diagnostic);
}

pub fn diagnostics() -> Vec<Diagnostic> {
    DIAGNOSTICS.lock().drain().collect()
}
