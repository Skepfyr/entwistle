use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fmt::{self, Write as _},
    sync::Arc,
};

use indenter::indented;

use crate::Span;

mod parser;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ident(pub Arc<str>);

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Language {
    pub definitions: HashMap<Ident, Definition>,
    pub tests: Vec<Test>,
}

impl Language {
    pub fn parse(input: &str) -> Self {
        parser::parse_grammar(input)
    }

    pub fn dependencies(&self, ident: Ident) -> HashSet<Ident> {
        let mut dependencies = HashSet::new();
        let mut visited = HashSet::new();
        let mut next = vec![ident];
        while let Some(ident) = next.pop() {
            for dep in self.direct_dependencies(&ident) {
                dependencies.insert(dep.clone());
                if visited.insert(dep.clone()) {
                    next.push(dep);
                }
            }
        }
        dependencies
    }

    fn direct_dependencies(&self, ident: &Ident) -> HashSet<Ident> {
        let mut dependencies = HashSet::new();
        fn production_deps(dependencies: &mut HashSet<Ident>, production: &Rule) {
            production
                .alternatives
                .iter()
                .flat_map(|expression| expression.sequence.iter())
                .for_each(|(term, _, _)| match term {
                    Item::Ident { ident, .. } => {
                        dependencies.insert(ident.clone());
                    }
                    Item::Group(production) => production_deps(dependencies, production),
                    _ => {}
                })
        }
        for rule in &self.definitions[ident].rules {
            production_deps(&mut dependencies, rule)
        }
        dependencies
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
    pub silent: bool,
    pub atomic: bool,
    pub ident: Ident,
    pub generics: Vec<Ident>,
    pub span: Span,
    pub rules: Vec<Rule>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Rule {
    pub span: Span,
    pub alternatives: BTreeSet<Expression>,
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, expression) in self.alternatives.iter().enumerate() {
            if i > 0 {
                f.write_str(" | ")?;
            }
            write!(f, "{expression}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Expression {
    pub span: Span,
    pub sequence: Vec<(Item, Quantifier, Span)>,
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, (item, quantifier, _)) in self.sequence.iter().enumerate() {
            if i > 0 {
                f.write_char(' ')?;
            }
            write!(f, "{item}{quantifier}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Item {
    Ident {
        mark: Mark,
        ident: Ident,
        generics: Vec<Rule>,
    },
    String(String),
    Regex(String),
    Group(Rule),
    Lookaround(LookaroundType, Rule),
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Item::Ident {
                mark,
                ident,
                generics,
            } => {
                write!(f, "{mark}{ident}")?;
                if !generics.is_empty() {
                    write!(f, "<")?;
                    for (i, generic) in generics.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{generic}")?;
                    }
                    write!(f, ">")?;
                }
            }
            Item::String(string) => {
                write!(f, "{string:?}")?;
            }
            Item::Regex(regex) => {
                write!(f, "/{regex}/")?;
            }
            Item::Group(rule) => {
                write!(f, "({rule})")?;
            }
            Item::Lookaround(lookaround_type, rule) => {
                write!(f, "({lookaround_type} {rule})")?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LookaroundType {
    pub positive: bool,
    pub ahead: bool,
    pub span: Span,
}

impl fmt::Display for LookaroundType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.positive {
            write!(f, "!")?;
        }
        if self.ahead {
            write!(f, ">>")?;
        } else {
            write!(f, "<<")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Quantifier {
    Once,
    AtMostOnce,
    AtLeastOnce,
    Any,
}

impl fmt::Display for Quantifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Quantifier::Once => {}
            Quantifier::AtMostOnce => f.write_char('?')?,
            Quantifier::AtLeastOnce => f.write_char('+')?,
            Quantifier::Any => f.write_char('*')?,
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Mark {
    Super,
    This,
    Sub,
}

impl fmt::Display for Mark {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Mark::Super => f.write_char('$')?,
            Mark::This => {}
            Mark::Sub => f.write_char('~')?,
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Test {
    pub goal: Rule,
    pub test: Arc<str>,
    pub test_span: Span,
    pub parse_trees: Vec<ParseTree>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseTree {
    Leaf { ident: Option<Ident>, data: String },
    Node { ident: Ident, nodes: Vec<ParseTree> },
}

impl fmt::Display for ParseTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseTree::Leaf { ident, data } => {
                if let Some(ident) = ident {
                    write!(f, "{ident}: ")?;
                }
                writeln!(f, "{data:?}")?;
            }
            ParseTree::Node { ident, nodes } => {
                writeln!(f, "{ident}:")?;
                let mut indented = indented(f).with_str("  ");
                for node in nodes {
                    write!(indented, "{node}")?;
                }
            }
        }
        Ok(())
    }
}

impl ParseTree {
    pub fn ident(&self) -> Option<&Ident> {
        match self {
            ParseTree::Leaf { ident, .. } => ident.as_ref(),
            ParseTree::Node { ident, .. } => Some(ident),
        }
    }

    pub fn data(&self) -> String {
        match self {
            ParseTree::Leaf { data, .. } => data.clone(),
            ParseTree::Node { nodes, .. } => nodes.iter().map(ParseTree::data).collect(),
        }
    }
}
