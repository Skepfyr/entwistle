use std::{
    fmt::{self, Write},
    hash::Hash,
    str,
    sync::Arc,
};

use im::{OrdMap, OrdSet};

use crate::{
    language::{self, Ident, Language, Mark, Quantifier},
    util::DbDisplay,
};

#[salsa::query_group(LowerStorage)]
pub trait Lower: Language {
    #[salsa::interned]
    fn intern_non_terminal(&self, data: NonTerminalData) -> NonTerminal;
    #[salsa::interned]
    fn intern_terminal(&self, data: TerminalData) -> Terminal;
    fn production(&self, non_terminal: NonTerminal) -> Production;
    fn terminal(&self, ident: Ident) -> Terminal;
    fn term(&self, ident: Ident) -> Term;
    fn lower_production(
        &self,
        term: language::Production,
        current_name: Name,
        scope: Scope,
    ) -> OrdSet<Arc<[UnresolvedTerm]>>;
    fn lower_atomic_ident(&self, ident: Ident) -> Arc<str>;
    fn lower_term(
        &self,
        term: language::Term,
        quantifier: language::Quantifier,
        current_name: Name,
        scope: Scope,
    ) -> UnresolvedTerm;
}

pub fn production(db: &dyn Lower, non_terminal: NonTerminal) -> Production {
    let (name, scope) = match db.lookup_intern_non_terminal(non_terminal) {
        NonTerminalData::Goal { non_terminal } => {
            return [Arc::new([
                Term::NonTerminal(non_terminal),
                Term::Terminal(db.intern_terminal(TerminalData::EndOfInput { goal: non_terminal })),
            ]) as Arc<[_]>]
            .into_iter()
            .collect()
        }
        NonTerminalData::Named { name, scope } => (name, scope),
        NonTerminalData::Anonymous { production } => {
            return production
                .into_iter()
                .map(|terms| {
                    terms
                        .iter()
                        .map(|term| term.resolve_this(non_terminal))
                        .collect::<Arc<[_]>>()
                })
                .collect()
        }
    };
    let rules = db.rules(name.ident);
    let rule = match &*rules {
        [rule] => rule,
        _ => panic!("Should have exactly one rule"),
    };
    let mut production = db
        .lower_production(rule.productions[name.index].clone(), name, scope.clone())
        .into_iter()
        .map(|terms| {
            terms
                .iter()
                .map(|term| term.resolve_this(non_terminal))
                .collect::<Arc<[_]>>()
        })
        .collect::<Production>();
    if name.index < rule.productions.len() - 1 {
        production.insert(Arc::new([Term::NonTerminal(db.intern_non_terminal(
            NonTerminalData::Named {
                name: Name {
                    ident: name.ident,
                    index: name.index + 1,
                },
                scope,
            },
        ))]));
    }
    production
}

pub fn terminal(db: &dyn Lower, ident: Ident) -> Terminal {
    assert!(db.is_atomic(ident));
    db.intern_terminal(TerminalData::Real {
        name: Some(ident),
        data: db.lower_atomic_ident(ident),
    })
}

pub fn term(db: &dyn Lower, ident: Ident) -> Term {
    let rules = db.rules(ident);
    let rule = match &*rules {
        [rule] => rule,
        _ => {
            return Term::Terminal(db.intern_terminal(TerminalData::Real {
                name: Some(ident),
                data: "".into(),
            }))
        }
    };
    assert_eq!(ident, rule.ident);
    if rule.atomic {
        Term::Terminal(db.terminal(ident))
    } else {
        let name = Name {
            ident: rule.ident,
            index: 0,
        };
        Term::NonTerminal(db.intern_non_terminal(NonTerminalData::Named {
            name,
            scope: Scope::default(),
        }))
    }
}

fn lower_production(
    db: &dyn Lower,
    production: language::Production,
    current_name: Name,
    scope: Scope,
) -> OrdSet<Arc<[UnresolvedTerm]>> {
    production
        .alternatives
        .into_iter()
        .map(|expression| {
            expression
                .sequence
                .into_iter()
                .map(|(term, quantifier)| {
                    db.lower_term(term, quantifier, current_name, scope.clone())
                })
                .collect::<Arc<[UnresolvedTerm]>>()
        })
        .collect()
}

fn lower_term(
    db: &dyn Lower,
    term: language::Term,
    quantifier: language::Quantifier,
    current_name: Name,
    scope: Scope,
) -> UnresolvedTerm {
    if quantifier != Quantifier::Once {
        let term = db.lower_term(term, Quantifier::Once, current_name, scope);
        let mut production: OrdSet<Arc<[UnresolvedTerm]>> = OrdSet::new();
        // Zero times
        if let Quantifier::Any | Quantifier::AtMostOnce = quantifier {
            production.insert(Arc::new([]));
        }
        // One time
        if let Quantifier::AtMostOnce = quantifier {
            production.insert(Arc::new([term]));
        }
        // Many times
        if let Quantifier::Any | Quantifier::AtLeastOnce = quantifier {
            production.insert(Arc::new([term, UnresolvedTerm::This]));
        }
        return UnresolvedTerm::NonTerminal(
            db.intern_non_terminal(NonTerminalData::Anonymous { production }),
        );
    }

    match term {
        language::Term::Ident { mark, ident } => {
            if db.is_atomic(ident) {
                UnresolvedTerm::Terminal(db.terminal(ident))
            } else {
                let marked_name = Name {
                    ident: current_name.ident,
                    index: match mark {
                        Mark::Super => 0,
                        Mark::This => current_name.index,
                        Mark::Sub => current_name.index + 1,
                    },
                };
                let non_terminal = if ident == current_name.ident {
                    NonTerminalData::Named {
                        name: marked_name,
                        scope,
                    }
                } else {
                    let mut minimizer = db.dependencies(ident);
                    minimizer.remove(&ident);
                    NonTerminalData::Named {
                        name: scope.get(ident),
                        scope: scope.sub_scope(marked_name, minimizer),
                    }
                };
                UnresolvedTerm::NonTerminal(db.intern_non_terminal(non_terminal))
            }
        }
        language::Term::String(string) => {
            UnresolvedTerm::Terminal(db.intern_terminal(TerminalData::Real {
                name: None,
                data: string.into(),
            }))
        }
        language::Term::Regex(regex) => {
            UnresolvedTerm::Terminal(db.intern_terminal(TerminalData::Real {
                name: None,
                data: regex.to_string().into(),
            }))
        }
        language::Term::Group(production) => {
            UnresolvedTerm::NonTerminal(db.intern_non_terminal(NonTerminalData::Anonymous {
                production: db.lower_production(production, current_name, scope),
            }))
        }
    }
}

fn lower_atomic_ident(db: &dyn Lower, ident: Ident) -> Arc<str> {
    let rules = db.rules(ident);
    let rule = match &*rules {
        [rule] => rule,
        _ => return "".into(),
    };

    let mut regex = String::new();
    for (i, production) in rule.productions.iter().enumerate() {
        if i > 0 {
            regex.push('|');
        }
        regex.push('(');
        write_production_regex(db, &mut regex, production);
        regex.push(')');
    }

    regex.into()
}

fn write_production_regex(db: &dyn Lower, regex: &mut String, production: &language::Production) {
    for (i, expression) in production.alternatives.iter().enumerate() {
        if i > 0 {
            regex.push('|');
        }
        regex.push('(');
        for &(ref term, quantifier) in &expression.sequence {
            regex.push('(');

            match term {
                language::Term::Ident { ident, .. } => {
                    regex.push_str(&db.lower_atomic_ident(*ident))
                }
                language::Term::String(s) => {
                    regex.reserve(s.len());
                    for c in s.chars() {
                        if let '^' | '$' | '*' | '+' | '?' | '.' | '(' | ')' | '[' | ']' | '{'
                        | '}' | '|' = c
                        {
                            regex.push('\\');
                        }
                        regex.push(c);
                    }
                }
                language::Term::Regex(r) => regex.push_str(r.as_str()),
                language::Term::Group(production) => write_production_regex(db, regex, production),
            }

            let _ = write!(
                regex,
                "){}",
                match quantifier {
                    Quantifier::Once => "",
                    Quantifier::AtMostOnce => "?",
                    Quantifier::AtLeastOnce => "+",
                    Quantifier::Any => "*",
                }
            );
        }
        regex.push(')');
    }
}

intern_key!(NonTerminal);

impl<Db: Lower> DbDisplay<Db> for NonTerminal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result {
        match db.lookup_intern_non_terminal(*self) {
            NonTerminalData::Goal { non_terminal } => {
                write!(f, "Goal({})", non_terminal.display(db))?;
            }
            NonTerminalData::Named { name, scope } => {
                write!(f, "{}#{}{{", db.lookup_intern_ident(name.ident), name.index)?;
                for (key, Name { ident, index }) in scope.ident_map {
                    write!(
                        f,
                        "{}: {}#{}, ",
                        db.lookup_intern_ident(key),
                        db.lookup_intern_ident(ident),
                        index
                    )?;
                }
                write!(f, "}}")?;
            }
            NonTerminalData::Anonymous { .. } => write!(f, "#{}", self.0)?,
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NonTerminalData {
    Goal {
        non_terminal: NonTerminal,
    },
    Named {
        name: Name,
        scope: Scope,
    },
    Anonymous {
        production: OrdSet<Arc<[UnresolvedTerm]>>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name {
    pub ident: Ident,
    pub index: usize,
}

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Scope {
    pub ident_map: OrdMap<Ident, Name>,
}

impl Scope {
    fn get(&self, ident: Ident) -> Name {
        self.ident_map
            .get(&ident)
            .copied()
            .unwrap_or(Name { ident, index: 0 })
    }

    fn sub_scope(&self, scope_addition: Name, minimizer: OrdSet<Ident>) -> Self {
        let mut ident_map = OrdMap::new();
        if minimizer.contains(&scope_addition.ident) && scope_addition.index != 0 {
            ident_map.insert(scope_addition.ident, scope_addition);
        }
        for ident in minimizer {
            if let Some(&name) = self.ident_map.get(&ident) {
                ident_map.insert(ident, name);
            }
        }
        Scope { ident_map }
    }
}

intern_key!(Terminal);

impl<Db: Lower> DbDisplay<Db> for Terminal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result {
        match db.lookup_intern_terminal(*self) {
            TerminalData::Real { name, data } => {
                if let Some(name) = name {
                    write!(f, "{}(", db.lookup_intern_ident(name))?;
                } else {
                    write!(f, "#{}(", self.0)?;
                }
                write!(f, "{:?})", data)?;
            }
            TerminalData::EndOfInput { goal } => write!(f, "EoI({})", goal.display(db))?,
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TerminalData {
    Real { name: Option<Ident>, data: Arc<str> },
    EndOfInput { goal: NonTerminal },
}

pub type Production = OrdSet<Arc<[Term]>>;

impl<Db: Lower> DbDisplay<Db> for Production {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result {
        for (i, alt) in self.iter().enumerate() {
            if i != 0 {
                write!(f, "| ")?;
            }
            if alt.is_empty() {
                write!(f, "() ")?;
            }
            for &term in &**alt {
                write!(f, "{} ", term.display(db))?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term {
    Terminal(Terminal),
    NonTerminal(NonTerminal),
}

impl<Db: Lower> DbDisplay<Db> for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &Db) -> fmt::Result {
        match *self {
            Term::Terminal(t) => t.fmt(f, db),
            Term::NonTerminal(nt) => nt.fmt(f, db),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnresolvedTerm {
    Terminal(Terminal),
    NonTerminal(NonTerminal),
    This,
}

impl UnresolvedTerm {
    pub fn resolve_this(self, this: NonTerminal) -> Term {
        match self {
            UnresolvedTerm::Terminal(t) => Term::Terminal(t),
            UnresolvedTerm::NonTerminal(nt) => Term::NonTerminal(nt),
            UnresolvedTerm::This => Term::NonTerminal(this),
        }
    }
}
