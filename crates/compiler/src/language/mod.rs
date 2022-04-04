use std::{collections::HashSet, hash, sync::Arc};

use im::{OrdMap, OrdSet};
use regex::Regex;

use crate::file::Files;

mod parser;

#[salsa::query_group(LanguageStorage)]
pub trait Language: Files {
    #[salsa::interned]
    fn intern_ident(&self, name: String) -> Ident;
    #[salsa::invoke(parser::parse_grammar)]
    fn parse_grammar(&self) -> Grammar;
    fn idents(&self) -> Arc<[Ident]>;
    fn rules(&self, ident: Ident) -> Arc<[Rule]>;
    fn tests(&self, ident: Ident) -> Arc<[Test]>;
    fn is_atomic(&self, ident: Ident) -> bool;
    fn dependencies(&self, ident: Ident) -> OrdSet<Ident>;
    fn direct_dependencies(&self, ident: Ident) -> OrdSet<Ident>;
}

fn idents(db: &dyn Language) -> Arc<[Ident]> {
    db.parse_grammar().rules.keys().copied().collect()
}

fn rules(db: &dyn Language, ident: Ident) -> Arc<[Rule]> {
    db.parse_grammar()
        .rules
        .get(&ident)
        .cloned()
        .unwrap_or_else(|| Arc::new([]))
}

fn tests(db: &dyn Language, ident: Ident) -> Arc<[Test]> {
    db.parse_grammar()
        .tests
        .get(&ident)
        .cloned()
        .unwrap_or_else(|| Arc::new([]))
}

fn is_atomic(db: &dyn Language, ident: Ident) -> bool {
    db.rules(ident).first().map_or(true, |rule| rule.atomic)
}

fn dependencies(db: &dyn Language, ident: Ident) -> OrdSet<Ident> {
    let mut dependencies = OrdSet::new();
    let mut visited = HashSet::new();
    let mut next = vec![ident];
    while let Some(ident) = next.pop() {
        for dep in db.direct_dependencies(ident) {
            dependencies.insert(dep);
            if !visited.contains(&dep) {
                visited.insert(ident);
                next.push(dep);
            }
        }
    }
    dependencies
}

fn direct_dependencies(db: &dyn Language, ident: Ident) -> OrdSet<Ident> {
    let mut dependencies = OrdSet::new();
    let rules = db.rules(ident);
    fn production_deps(dependencies: &mut OrdSet<Ident>, production: &Production) {
        production
            .alternatives
            .iter()
            .flat_map(|expression| expression.sequence.iter())
            .for_each(|(term, _)| match term {
                Term::Ident { ident, .. } => {
                    dependencies.insert(*ident);
                }
                Term::Group(production) => production_deps(dependencies, production),
                _ => {}
            })
    }
    rules
        .iter()
        .flat_map(|rule| rule.productions.iter())
        .for_each(|production| production_deps(&mut dependencies, production));
    dependencies
}

intern_key!(Ident);

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Grammar {
    pub rules: OrdMap<Ident, Arc<[Rule]>>,
    pub tests: OrdMap<Ident, Arc<[Test]>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    pub ident: Ident,
    pub silent: bool,
    pub atomic: bool,
    pub productions: Vec<Production>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Production {
    pub alternatives: OrdSet<Expression>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Expression {
    pub sequence: Vec<(Term, Quantifier)>,
}

#[derive(Debug, Clone)]
pub enum Term {
    Ident { mark: Mark, ident: Ident },
    String(String),
    Regex(Regex),
    Group(Production),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
enum TermOrd<'a> {
    Ident { mark: Mark, ident: Ident },
    String(&'a str),
    Regex(&'a str),
    Group(&'a Production),
}

impl<'a> From<&'a Term> for TermOrd<'a> {
    fn from(term: &'a Term) -> Self {
        match term {
            Term::Ident { mark, ident } => TermOrd::Ident {
                mark: *mark,
                ident: *ident,
            },
            Term::String(s) => TermOrd::String(s),
            Term::Regex(r) => TermOrd::Regex(r.as_str()),
            Term::Group(group) => TermOrd::Group(group),
        }
    }
}
impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        PartialEq::eq(&TermOrd::from(self), &other.into())
    }
}
impl Eq for Term {}
impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Term {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&TermOrd::from(self), &other.into())
    }
}
impl hash::Hash for Term {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        hash::Hash::hash(&TermOrd::from(self), state)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Quantifier {
    Once,
    AtMostOnce,
    AtLeastOnce,
    Any,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Mark {
    Super,
    This,
    Sub,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Test {
    ident: Ident,
    test: Arc<str>,
    parse_tree: ParseTree,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseTree {
    Leaf {
        ident: Option<Ident>,
        data: Arc<str>,
    },
    Node {
        ident: Ident,
        nodes: Arc<[ParseTree]>,
    },
}
