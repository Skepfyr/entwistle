use std::{
    collections::HashSet,
    fmt::{self, Write},
    sync::Arc,
};

use salsa::Cycle;
use tracing::{instrument, trace, trace_span};

use crate::{
    language::Language,
    lower::{production, NonTerminal, Production, Term, TermKind, Terminal},
    util::DisplayWithDb,
    Db,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TermString {
    non_terminal: Option<NormalNonTerminal>,
    terms: Vec<NormalTerm>,
    next_term: usize,
    parent: Option<Arc<TermString>>,
    terminals_yielded: u32,
}

impl TermString {
    pub fn new(terms: &[Term]) -> Arc<Self> {
        Arc::new(Self {
            non_terminal: None,
            terms: terms.iter().map(|term| term.kind.clone().into()).collect(),
            next_term: 0,
            parent: None,
            terminals_yielded: 0,
        })
    }

    pub fn non_terminal(&self) -> Option<&NormalNonTerminal> {
        self.non_terminal.as_ref()
    }

    pub fn terminals_yielded(&self) -> u32 {
        self.terminals_yielded
    }

    pub fn self_and_parents(&self) -> impl Iterator<Item = &Self> {
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
    type Item = (Option<Terminal>, Arc<TermString>);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(mut term_string) = self.stack.pop() {
            let span = trace_span!("next", term_string = %term_string.display(self.db));
            let _guard = span.enter();
            if let Some(term) = term_string.terms.get(term_string.next_term).cloned() {
                let new = Arc::make_mut(&mut term_string);
                new.next_term += 1;
                match term {
                    NormalTerm::Terminal(terminal) => {
                        new.terminals_yielded += 1;
                        //trace!(terminal = %terminal.display(self.db), "Found terminal");
                        return Some((Some(terminal), term_string));
                    }
                    NormalTerm::NonTerminal(non_terminal) => {
                        //trace!(non_terminal = %non_terminal.display(self.db), "Walking down into non-terminal");
                        self.stack.extend(
                            normal_production(self.db, self.grammar, non_terminal.clone())
                                .iter()
                                .map(|terms| {
                                    Arc::new(TermString {
                                        non_terminal: Some(non_terminal.clone()),
                                        terms: terms.clone(),
                                        next_term: 0,
                                        parent: Some(term_string.clone()),
                                        terminals_yielded: 0,
                                    })
                                }),
                        )
                    }
                }
            } else if let Some(mut parent) = term_string.parent.as_ref().cloned() {
                //trace!("Walking up to parent");
                Arc::make_mut(&mut parent).terminals_yielded += term_string.terminals_yielded;
                self.stack.push(parent);
            } else {
                //trace!("Reached end of term string");
                return Some((None, term_string));
            }
        }
        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NormalNonTerminal {
    Original(NonTerminal),
    Minus(NonTerminal, TermKind),
}

impl DisplayWithDb for NormalNonTerminal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        let (NormalNonTerminal::Original(non_terminal) | NormalNonTerminal::Minus(non_terminal, _)) =
            self;
        write!(f, "{}", non_terminal.display(db))?;
        if let NormalNonTerminal::Minus(_, minus) = self {
            write!(f, "-{}", minus.display(db))?;
        }
        Ok(())
    }
}

impl From<NonTerminal> for NormalNonTerminal {
    fn from(nt: NonTerminal) -> Self {
        Self::Original(nt)
    }
}

impl NormalNonTerminal {
    fn base(&self) -> NonTerminal {
        match *self {
            NormalNonTerminal::Original(nt) => nt,
            NormalNonTerminal::Minus(nt, _) => nt,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NormalTerm {
    Terminal(Terminal),
    NonTerminal(NormalNonTerminal),
}

impl DisplayWithDb for NormalTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        match self {
            NormalTerm::Terminal(terminal) => {
                write!(f, "{}", terminal.display(db))
            }
            NormalTerm::NonTerminal(non_terminal) => {
                write!(f, "{}", non_terminal.display(db))
            }
        }
    }
}

impl From<TermKind> for NormalTerm {
    fn from(t: TermKind) -> Self {
        match t {
            TermKind::Terminal(t) => Self::Terminal(t),
            TermKind::NonTerminal(nt) => Self::NonTerminal(nt.into()),
        }
    }
}

#[instrument(skip_all, fields(non_terminal = %non_terminal.display(db)))]
#[salsa::tracked(return_ref)]
pub fn normal_production(
    db: &dyn Db,
    language: Language,
    non_terminal: NormalNonTerminal,
) -> HashSet<Vec<NormalTerm>> {
    let original_production = production(db, language, non_terminal.base());
    trace!(production = %original_production.display(db), "Normalizing production");
    match non_terminal {
        NormalNonTerminal::Original(non_terminal) => {
            if left_recursive(db, language, non_terminal) {
                // 1 - Moor00 5
                proper_left_corners(db, language, non_terminal)
                    .into_iter()
                    .filter(|term| {
                        !matches!(term, TermKind::NonTerminal(nt) if left_recursive(db, language, *nt))
                    })
                    .map(|term| {
                        vec![
                            term.clone().into(),
                            NormalTerm::NonTerminal(NormalNonTerminal::Minus(non_terminal, term)),
                        ]
                    })
                    .collect()
            } else {
                // 4 - Moor00 5
                original_production
                    .alternatives(db)
                    .iter()
                    .map(|alternative| {
                        alternative
                            .terms(db)
                            .iter()
                            .map(|term| term.kind.clone().into())
                            .collect::<Vec<_>>()
                    })
                    .collect()
            }
        }
        NormalNonTerminal::Minus(non_terminal, ref symbol) => {
            assert!(left_recursive(db, language, non_terminal));
            // 2 & 3 - Moor00 5
            // This definitely includes non_terminal as it's left recursive.
            proper_left_corners(db, language, non_terminal)
                .into_iter()
                .filter_map(|term| match term {
                    TermKind::NonTerminal(nt) if left_recursive(db, language, nt) => Some(nt),
                    _ => None,
                })
                .flat_map(|nt| {
                    production(db, language, nt)
                        .alternatives(db)
                        .iter()
                        .flat_map(|alternative| {
                            std::iter::successors(Some(alternative.terms(db).as_slice()), |terms| {
                                match terms {
                                    [head, tail @ ..] => {
                                        can_be_empty(db, language, &head.kind).then_some(tail)
                                    }
                                    [] => None,
                                }
                            })
                        })
                        .filter_map(move |alternative| match alternative {
                            [head, tail @ ..] if head.kind == *symbol => Some(
                                tail.iter()
                                    .map(|term| term.kind.clone().into())
                                    .chain((non_terminal != nt).then_some(NormalTerm::NonTerminal(
                                        NormalNonTerminal::Minus(
                                            non_terminal,
                                            TermKind::NonTerminal(nt),
                                        ),
                                    )))
                                    .collect::<Vec<_>>(),
                            ),
                            _ => None,
                        })
                })
                .collect()
        }
    }
}

fn left_recursive(db: &dyn Db, language: Language, non_terminal: NonTerminal) -> bool {
    proper_left_corners(db, language, non_terminal).contains(&TermKind::NonTerminal(non_terminal))
}

fn proper_left_corners(
    db: &dyn Db,
    language: Language,
    non_terminal: NonTerminal,
) -> HashSet<TermKind> {
    let mut left_corners = HashSet::new();
    let mut todo = vec![non_terminal];

    while let Some(nt) = todo.pop() {
        for alternative in production(db, language, nt).alternatives(db) {
            let mut terms = alternative.terms(db).iter().map(|term| &term.kind);
            let mut prev_empty = true;
            while prev_empty {
                let Some(term) = terms.next() else { break };
                prev_empty &= can_be_empty(db, language, term);
                let new_term = left_corners.insert(term.clone());
                match term {
                    TermKind::NonTerminal(next) if new_term && *next != non_terminal => {
                        todo.push(*next);
                    }
                    _ => {}
                }
            }
        }
    }

    trace!(
        non_terminal = %non_terminal.display(db),
        left_corners = %left_corners.iter().map(|term| format!("{} ", term.display(db))).collect::<String>(),
        "Computed proper left corners"
    );
    left_corners
}

#[instrument(skip_all, fields(term = %term.display(db)))]
pub fn can_be_empty(db: &dyn Db, language: Language, term: &TermKind) -> bool {
    match term {
        TermKind::Terminal(_) => false,
        TermKind::NonTerminal(nt) => {
            can_production_be_empty(db, language, production(db, language, *nt))
        }
    }
}

#[salsa::tracked(recovery_fn=recover_can_be_empty)]
pub fn can_production_be_empty(db: &dyn Db, language: Language, production: Production) -> bool {
    let can_be_empty = production.alternatives(db).iter().any(|alternative| {
        alternative
            .terms(db)
            .iter()
            .all(|term| can_be_empty(db, language, &term.kind))
    });
    if can_be_empty {
        trace!(production = %production.display(db), "Production can be empty");
    } else {
        trace!(production = %production.display(db), "Production cannot be empty");
    }
    can_be_empty
}

fn recover_can_be_empty(db: &dyn Db, _cycle: &Cycle, language: Language, p: Production) -> bool {
    fn inner(
        db: &dyn Db,
        language: Language,
        p: Production,
        visited: &mut HashSet<Production>,
    ) -> bool {
        p.alternatives(db).iter().any(|alternative| {
            alternative.terms(db).iter().all(|term| {
                let TermKind::NonTerminal(nt) = term.kind else {
                    return false;
                };
                let production = production(db, language, nt);
                if visited.insert(production) {
                    let res = inner(db, language, production, visited);
                    visited.remove(&production);
                    res
                } else {
                    false
                }
            })
        })
    }
    let can_be_empty = inner(db, language, p, &mut HashSet::new());
    if can_be_empty {
        trace!(production = %p.display(db), "Cycle recovery: Production can be empty");
    } else {
        trace!(production = %p.display(db), "Cycle recovery: Production cannot be empty");
    }
    can_be_empty
}
