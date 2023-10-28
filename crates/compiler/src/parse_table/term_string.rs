use std::{
    fmt::{self, Write},
    sync::Arc,
};

use tracing::trace;

use crate::{
    language::Language,
    lower::TerminalUse,
    parse_table::{normal_production, NormalTerm},
    util::DisplayWithDb,
    Db,
};

use super::NormalNonTerminal;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TermString {
    pub non_terminal: Option<NormalNonTerminal>,
    terms: Vec<NormalTerm>,
    next_term: usize,
    parent: Option<Arc<TermString>>,
}

impl TermString {
    pub fn new(non_terminal: Option<NormalNonTerminal>, terms: Vec<NormalTerm>, next_term: usize) -> Arc<Self> {
        Arc::new(Self {
            non_terminal,
            terms,
            next_term,
            parent: None,
        })
    }

    pub fn parents(&self) -> impl Iterator<Item = &Self> {
        std::iter::successors(Some(self), |term_string| term_string.parent.as_deref())
    }

    pub fn next(self: Arc<Self>, db: &dyn Db, language: Language) -> Iter<'_> {
        Iter::new(self, db, language)
    }
}

impl DisplayWithDb for TermString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        fn display(
            this: &TermString,
            f: &mut fmt::Formatter<'_>,
            db: &dyn Db,
            child: &mut dyn FnMut(&mut fmt::Formatter) -> fmt::Result,
        ) -> fmt::Result {
            let mut fmt_this = move |f: &mut fmt::Formatter<'_>| {
                for (i, term) in this.terms[..this.next_term].iter().enumerate() {
                    if i != 0 {
                        f.write_char(' ')?;
                    }
                    write!(f, "{}", term.display(db))?;
                }
                f.write_char('(')?;
                child(f)?;
                f.write_char(')')?;
                for term in &this.terms[this.next_term..] {
                    write!(f, " {}", term.display(db))?;
                }
                Ok(())
            };
            if let Some(parent) = &this.parent {
                display(parent, f, db, &mut fmt_this)
            } else {
                fmt_this(f)
            }
        }
        display(self, f, db, &mut |_| Ok(()))
    }
}

#[derive(Clone)]
pub struct Iter<'a> {
    stack: Vec<Arc<TermString>>,
    db: &'a dyn Db,
    grammar: Language,
}

impl<'a> Iter<'a> {
    fn new(term_string: Arc<TermString>, db: &'a dyn Db, grammar: Language) -> Self {
        Self {
            stack: vec![term_string],
            db,
            grammar,
        }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = (Option<TerminalUse>, Arc<TermString>);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(mut term_string) = self.stack.pop() {
            if let Some(term) = term_string.terms.get(term_string.next_term).cloned() {
                Arc::make_mut(&mut term_string).next_term += 1;
                match term {
                    NormalTerm::Terminal(terminal) => {
                        trace!(terminal = %terminal.display(self.db), "Found terminal");
                        return Some((Some(terminal), term_string));
                    }
                    NormalTerm::NonTerminal(non_terminal) => {
                        trace!(non_terminal = %non_terminal.display(self.db), "Walking down into non-terminal");
                        self.stack.extend(
                            normal_production(self.db, self.grammar, &non_terminal)
                                .into_iter()
                                .map(|terms| {
                                    Arc::new(TermString {
                                        non_terminal: Some(non_terminal.clone()),
                                        terms,
                                        next_term: 0,
                                        parent: Some(term_string.clone()),
                                    })
                                }),
                        )
                    }
                }
            } else if let Some(parent) = &term_string.parent {
                trace!("Walking up to parent");
                self.stack.push(parent.clone());
            } else {
                trace!("Reached end of term string");
                return Some((None, term_string));
            }
        }
        None
    }
}
