use std::{
    fmt::{self, Write},
    sync::Arc,
};

use tracing::trace;

use crate::{
    lower::Terminal,
    parse_table::{normal_production, NormalTerm}, language::Language,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TermString {
    terms: Vec<NormalTerm>,
    next_term: usize,
    parent: Option<Arc<TermString>>,
}

impl TermString {
    pub fn new(terms: Vec<NormalTerm>, next_term: usize) -> Arc<Self> {
        Arc::new(Self {
            terms,
            next_term,
            parent: None,
        })
    }

    pub fn next(self: Arc<Self>, language: &Language) -> Iter {
        Iter::new(self, language)
    }
}

impl fmt::Display for TermString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn display(
            this: &TermString,
            f: &mut fmt::Formatter<'_>,
            child: &mut dyn FnMut(&mut fmt::Formatter) -> fmt::Result,
        ) -> fmt::Result {
            let mut fmt_this = move |f: &mut fmt::Formatter<'_>| {
                for (i, term) in this.terms[..this.next_term].iter().enumerate() {
                    if i != 0 {
                        f.write_char(' ')?;
                    }
                    write!(f, "{term}")?;
                }
                f.write_char('(')?;
                child(f)?;
                f.write_char(')')?;
                for term in &this.terms[this.next_term..] {
                    write!(f, " {term}")?;
                }
                Ok(())
            };
            if let Some(parent) = &this.parent {
                display(parent, f, &mut fmt_this)
            } else {
                fmt_this(f)
            }
        }
        display(self, f, &mut |_| Ok(()))
    }
}

#[derive(Debug, Clone)]
pub struct Iter<'a> {
    stack: Vec<Arc<TermString>>,
    grammar: &'a Language,
}

impl<'a> Iter<'a> {
    fn new(term_string: Arc<TermString>, grammar: &'a Language) -> Self {
        Self {
            stack: vec![term_string],
            grammar,
        }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = (Option<Terminal>, Arc<TermString>);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(mut term_string) = self.stack.pop() {
            if let Some(term) = term_string.terms.get(term_string.next_term).cloned() {
                Arc::make_mut(&mut term_string).next_term += 1;
                match term {
                    NormalTerm::Terminal(terminal) => {
                        trace!(%terminal, "Found terminal");
                        return Some((Some(terminal), term_string));
                    }
                    NormalTerm::NonTerminal(non_terminal) => {
                        trace!(%non_terminal, "Walking down into non-terminal");
                        self.stack.extend(
                            normal_production(self.grammar, &non_terminal)
                                .into_iter()
                                .map(|terms| {
                                    Arc::new(TermString {
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
