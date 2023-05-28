use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fmt::{self, Write as _},
    sync::Arc,
};

use indenter::indented;

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
    pub definitions: HashMap<Ident, Vec<Definition>>,
    pub tests: HashMap<Ident, Vec<Test>>,
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
                .for_each(|(term, _)| match term {
                    Item::Ident { ident, .. } => {
                        dependencies.insert(ident.clone());
                    }
                    Item::Group(production) => production_deps(dependencies, production),
                    _ => {}
                })
        }
        self.definitions[ident]
            .iter()
            .flat_map(|definition| &definition.rules)
            .for_each(|rule| production_deps(&mut dependencies, rule));
        dependencies
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
    pub ident: Ident,
    pub silent: bool,
    pub atomic: bool,
    pub rules: Vec<Rule>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Rule {
    pub alternatives: BTreeSet<Expression>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Expression {
    pub sequence: Vec<(Item, Quantifier)>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Item {
    Ident { mark: Mark, ident: Ident },
    String(String),
    Group(Rule),
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
    pub ident: Ident,
    pub test: Arc<str>,
    pub parse_tree: ParseTree,
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
