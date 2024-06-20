use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fmt::{self, Write as _},
};

use indenter::indented;

use crate::{diagnostics::emit, util::DisplayWithDb, Db, Span};

mod parser;

#[salsa::interned]
pub struct Ident<'db> {
    #[return_ref]
    pub name: String,
}

impl<'db> DisplayWithDb for Ident<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        f.write_str(self.name(db))
    }
}

#[salsa::input]
pub struct Source {
    #[return_ref]
    pub text: String,
}

#[salsa::tracked]
pub struct Language<'db> {
    #[return_ref]
    pub definitions: HashMap<Ident<'db>, Definition<'db>>,
    #[return_ref]
    pub tests: Vec<Test<'db>>,
}

#[salsa::tracked]
pub fn parse<'db>(db: &'db dyn Db, input: Source) -> Language<'db> {
    parser::parse_grammar(db, input.text(db))
}

#[salsa::tracked]
impl<'db> Language<'db> {
    #[salsa::tracked]
    pub fn definition(self, db: &'db dyn Db, ident: Ident<'db>, span: Span) -> Option<Definition<'db>> {
        match self.definitions(db).get(&ident).cloned() {
            Some(definition) => Some(definition),
            None => {
                emit("Identifier is not defined.", vec![(span, None)]);
                None
            }
        }
    }

    #[salsa::tracked]
    pub fn dependencies(self, db: &'db dyn Db, ident: Ident<'db>, span: Span) -> HashSet<Ident<'db>> {
        let mut dependencies = HashSet::new();
        let mut visited = HashSet::new();
        let mut next = vec![ident];
        while let Some(ident) = next.pop() {
            for dep in self.direct_dependencies(db, ident, span) {
                dependencies.insert(dep);
                if visited.insert(dep) {
                    next.push(dep);
                }
            }
        }
        dependencies
    }

    #[salsa::tracked]
    pub fn direct_dependencies(self, db: &'db dyn Db, ident: Ident<'db>, span: Span) -> HashSet<Ident<'db>> {
        fn production_deps<'db>(dependencies: &mut HashSet<Ident<'db>>, production: &Rule<'db>) {
            production
                .alternatives
                .iter()
                .flat_map(|expression| expression.sequence.iter())
                .for_each(|(term, _, _)| match term {
                    Item::Ident { ident, .. } => {
                        dependencies.insert(*ident);
                    }
                    Item::Group(production) => production_deps(dependencies, production),
                    _ => {}
                })
        }
        let mut dependencies = HashSet::new();
        let definition = match self.definition(db, ident, span) {
            Some(definition) => definition,
            None => return dependencies,
        };
        for rule in &definition.rules {
            production_deps(&mut dependencies, rule)
        }
        dependencies
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition<'db> {
    pub silent: bool,
    pub atomic: bool,
    pub ident: Ident<'db>,
    pub generics: Vec<Ident<'db>>,
    pub span: Span,
    pub rules: Vec<Rule<'db>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Rule<'db> {
    pub span: Span,
    pub alternatives: BTreeSet<Expression<'db>>,
}

impl<'db> DisplayWithDb for Rule<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        for (i, expression) in self.alternatives.iter().enumerate() {
            if i > 0 {
                f.write_str(" | ")?;
            }
            write!(f, "{}", expression.display(db))?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Expression<'db> {
    pub span: Span,
    pub sequence: Vec<(Item<'db>, Quantifier, Span)>,
}

impl<'db> DisplayWithDb for Expression<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        for (i, (item, quantifier, _)) in self.sequence.iter().enumerate() {
            if i > 0 {
                f.write_char(' ')?;
            }
            write!(f, "{}{}", item.display(db), quantifier)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Item<'db> {
    Ident {
        mark: Mark,
        ident: Ident<'db>,
        generics: Vec<Rule<'db>>,
    },
    String(String),
    Regex(String),
    Group(Rule<'db>),
    Lookaround(LookaroundType, Rule<'db>),
}

impl<'db> DisplayWithDb for Item<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        match self {
            Item::Ident {
                mark,
                ident,
                generics,
            } => {
                write!(f, "{}{}", mark, ident.display(db))?;
                if !generics.is_empty() {
                    write!(f, "<")?;
                    for (i, generic) in generics.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", generic.display(db))?;
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
                write!(f, "({})", rule.display(db))?;
            }
            Item::Lookaround(lookaround_type, rule) => {
                write!(f, "({} {})", lookaround_type, rule.display(db))?;
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

#[salsa::tracked]
pub struct Test<'db> {
    #[return_ref]
    pub goal: Rule<'db>,
    #[return_ref]
    pub test: String,
    pub test_span: Span,
    #[return_ref]
    pub parse_trees: Vec<ParseTree<'db>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseTree<'db> {
    Leaf { ident: Option<Ident<'db>>, data: String },
    Node { ident: Ident<'db>, nodes: Vec<ParseTree<'db>> },
}

impl<'db> DisplayWithDb for ParseTree<'db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, db: &dyn Db) -> fmt::Result {
        match self {
            ParseTree::Leaf { ident, data } => {
                if let Some(ident) = ident {
                    write!(f, "{}: ", ident.display(db))?;
                }
                writeln!(f, "{data:?}")?;
            }
            ParseTree::Node { ident, nodes } => {
                writeln!(f, "{}:", ident.display(db))?;
                let mut indented = indented(f).with_str("  ");
                for node in nodes {
                    write!(indented, "{}", node.display(db))?;
                }
            }
        }
        Ok(())
    }
}

impl<'db> ParseTree<'db> {
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
