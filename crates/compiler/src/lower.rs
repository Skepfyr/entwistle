use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    fmt::{self, Write as _},
    hash::Hash,
};

use regex_automata::nfa::thompson::NFA;

use crate::{
    language::{Definition, Expression, Ident, Item, Language, Mark, Quantifier, Rule},
    Span,
};

pub fn production(language: &Language, non_terminal: &NonTerminal) -> Production {
    match non_terminal {
        NonTerminal::Goal { ident } => {
            let definition: &Definition = match language.definitions[ident].as_slice() {
                [definition] => definition,
                _ => panic!("Should have exactly one rule"),
            };
            if !definition.generics.is_empty() {
                panic!("Unexpected generics for goal {ident}");
            }
            Production {
                alternatives: [vec![
                    Term {
                        kind: TermKind::NonTerminal(NonTerminal::Named {
                            name: Name {
                                ident: ident.clone(),
                                index: 0,
                            },
                            generics: Vec::new(),
                        }),
                        silent: definition.silent,
                        atomic: definition.atomic,
                    },
                    Term {
                        kind: TermKind::Terminal(Terminal::EndOfInput(ident.clone())),
                        silent: true,
                        atomic: true,
                    },
                ]]
                .into_iter()
                .map(Alternative::from)
                .collect(),
            }
        }
        NonTerminal::Named {
            name,
            generics: generic_parameters,
        } => {
            let definition: &Definition = match language.definitions[&name.ident].as_slice() {
                [definition] => definition,
                _ => panic!("Should have exactly one rule"),
            };
            if definition.generics.len() != generic_parameters.len() {
                panic!(
                    "Expected {} generics for {}, found {}",
                    definition.generics.len(),
                    name.ident,
                    generic_parameters.len()
                );
            }
            let generics = std::iter::Iterator::zip(
                definition.generics.iter().cloned(),
                generic_parameters.iter().cloned(),
            )
            .collect();
            if definition.rules.is_empty() {
                if name.index > 0 {
                    panic!(
                        "Unexpected index {} for empty definition for {}",
                        name.index, name.ident
                    );
                }
                return Production {
                    alternatives: vec![],
                };
            }
            fn contains_this_sub(this: &Ident, rule: &Rule) -> (bool, bool) {
                let mut contains_this = false;
                let mut contains_sub = false;
                for alternative in &rule.alternatives {
                    for (item, _, _) in &alternative.sequence {
                        match item {
                            Item::Ident {
                                mark,
                                ident,
                                generics: _,
                            } if ident == this => {
                                contains_this |= mark == &Mark::This;
                                contains_sub |= mark == &Mark::Sub;
                            }
                            Item::Group(inner_rule) => {
                                let (this, sub) = contains_this_sub(this, inner_rule);
                                contains_this |= this;
                                contains_sub |= sub;
                            }
                            _ => {}
                        }
                        if contains_this && contains_sub {
                            return (true, true);
                        }
                    }
                }
                (contains_this, contains_sub)
            }
            // Whether this rule contains a split below it.
            let splits = definition
                .rules
                .iter()
                .map(|rule| contains_this_sub(&name.ident, rule))
                .chain(Some((false, false)))
                .scan(false, |prev_split_below, (this, sub)| {
                    let split_above = *prev_split_below || this;
                    *prev_split_below = sub;
                    Some(split_above)
                })
                .skip(1);
            let mut index = name.index;
            let mut first = 0;
            let mut last = 0;
            for (i, split_below) in splits.enumerate() {
                last = i + 1;
                if split_below {
                    if index == 0 {
                        break;
                    }
                    index -= 1;
                    first = last;
                }
            }
            if index > 0 {
                panic!("Index {} out of bounds for {}", name.index, name.ident);
            }
            let mut alternatives: Vec<_> = definition.rules[first..last]
                .iter()
                .flat_map(|rule| lower_rule(language, rule, Some(name), &generics).alternatives)
                .collect();
            if last != definition.rules.len() {
                alternatives.push(
                    vec![Term {
                        kind: TermKind::NonTerminal(NonTerminal::Named {
                            name: Name {
                                ident: name.ident.clone(),
                                index: name.index + 1,
                            },
                            generics: generic_parameters.clone(),
                        }),
                        silent: true,
                        atomic: false,
                    }]
                    .into(),
                );
            }
            Production { alternatives }
        }
        NonTerminal::Anonymous {
            rule,
            context,
            generics,
        } => {
            if rule.alternatives.len() == 1
                && rule.alternatives.iter().next().unwrap().sequence.len() == 1
            {
                let (item, quantifier, span) =
                    &rule.alternatives.iter().next().unwrap().sequence[0];
                let term = lower_term(
                    language,
                    generics,
                    item,
                    Quantifier::Once,
                    *span,
                    context.as_ref(),
                );
                let mut alternatives: Vec<Alternative> = Vec::new();
                // Zero times
                if let Quantifier::Any | Quantifier::AtMostOnce = quantifier {
                    alternatives.push(vec![].into());
                }
                // One time
                if let Quantifier::AtMostOnce | Quantifier::AtLeastOnce | Quantifier::Once =
                    quantifier
                {
                    alternatives.push(vec![term.clone()].into());
                }
                // Many times
                if let Quantifier::Any | Quantifier::AtLeastOnce = quantifier {
                    alternatives.push(
                        vec![
                            Term {
                                kind: TermKind::NonTerminal(non_terminal.clone()),
                                silent: true,
                                atomic: false,
                            },
                            term,
                        ]
                        .into(),
                    );
                }
                Production { alternatives }
            } else {
                lower_rule(language, rule, context.as_ref(), generics)
            }
        }
    }
}

fn lower_rule(
    language: &Language,
    rule: &Rule,
    current_name: Option<&Name>,
    generics: &BTreeMap<Ident, NonTerminal>,
) -> Production {
    Production {
        alternatives: rule
            .alternatives
            .iter()
            .map(|expression| {
                let (sequence, lookahead) = match expression.sequence.last() {
                    Some((Item::Lookaround(lookaround_type, rule), Quantifier::Once, _)) => {
                        if lookaround_type.positive || !lookaround_type.ahead {
                            panic!("Only negative lookahead is supported");
                        }
                        (
                            &expression.sequence[..expression.sequence.len() - 1],
                            Some(NonTerminal::new_anonymous(
                                rule.clone(),
                                current_name,
                                generics.clone(),
                            )),
                        )
                    }
                    Some((Item::Lookaround(_, _), _, _)) => {
                        panic!("Lookaround cannot have a quantifier")
                    }
                    _ => (&expression.sequence[..], None),
                };
                let terms = sequence
                    .iter()
                    .map(|(term, quantifier, span)| {
                        lower_term(language, generics, term, *quantifier, *span, current_name)
                    })
                    .collect::<Vec<_>>();
                Alternative {
                    terms,
                    negative_lookahead: lookahead,
                }
            })
            .collect(),
    }
}

fn lower_term(
    language: &Language,
    generics: &BTreeMap<Ident, NonTerminal>,
    item: &Item,
    quantifier: Quantifier,
    span: Span,
    current_name: Option<&Name>,
) -> Term {
    if quantifier != Quantifier::Once {
        let mut alternatives = BTreeSet::new();
        alternatives.insert(Expression {
            sequence: vec![(item.clone(), quantifier, span)],
            span,
        });
        return Term {
            kind: TermKind::NonTerminal(NonTerminal::new_anonymous(
                Rule { alternatives, span },
                current_name,
                generics.clone(),
            )),
            silent: true,
            atomic: false,
        };
    }

    match item {
        Item::Ident {
            mark,
            ident,
            generics: generic_arguments,
        } => match generics.get(ident) {
            Some(nt) => Term {
                kind: TermKind::NonTerminal(nt.clone()),
                silent: true,
                atomic: false,
            },
            None => {
                let name = match current_name {
                    Some(current_name) if ident == &current_name.ident => Name {
                        ident: current_name.ident.clone(),
                        index: match mark {
                            Mark::Super => 0,
                            Mark::This => current_name.index,
                            Mark::Sub => current_name.index + 1,
                        },
                    },
                    _ => Name {
                        ident: ident.clone(),
                        index: 0,
                    },
                };
                let definition = match language.definitions.get(ident) {
                    Some(definitions) => &definitions[0],
                    None => panic!("{ident} is not defined"),
                };
                let generic_parameters = generic_arguments
                    .iter()
                    .map(|arg| {
                        NonTerminal::new_anonymous(arg.clone(), current_name, generics.clone())
                    })
                    .collect();
                Term {
                    kind: TermKind::NonTerminal(NonTerminal::Named {
                        name,
                        generics: generic_parameters,
                    }),
                    silent: definition.silent,
                    atomic: definition.atomic,
                }
            }
        },
        Item::String(data) => Term {
            kind: TermKind::Terminal(Terminal::new_token(regex_syntax::escape(data))),
            silent: false,
            atomic: true,
        },
        Item::Regex(regex) => Term {
            kind: TermKind::Terminal(Terminal::new_token(regex.clone())),
            silent: false,
            atomic: true,
        },
        Item::Group(rule) => Term {
            kind: TermKind::NonTerminal(NonTerminal::new_anonymous(
                rule.clone(),
                current_name,
                generics.clone(),
            )),
            silent: true,
            atomic: false,
        },
        Item::Lookaround(_, _) => {
            panic!("Only negative lookahead is supported at the end of an expression")
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NonTerminal {
    Goal {
        ident: Ident,
    },
    Named {
        name: Name,
        generics: Vec<NonTerminal>,
    },
    Anonymous {
        rule: Rule,
        context: Option<Name>,
        generics: BTreeMap<Ident, NonTerminal>,
    },
}

impl NonTerminal {
    fn new_anonymous(
        rule: Rule,
        context: Option<&Name>,
        generics: BTreeMap<Ident, NonTerminal>,
    ) -> NonTerminal {
        fn contains_non_super_ident(rule: &Rule, context: &Ident) -> bool {
            rule.alternatives
                .iter()
                .flat_map(|expression| &expression.sequence)
                .any(|(item, _, _)| match item {
                    Item::Ident {
                        mark,
                        ident,
                        generics: _,
                    } => ident == context && mark != &Mark::Super,
                    Item::String(_) | Item::Regex(_) => false,
                    Item::Group(rule) => contains_non_super_ident(rule, context),
                    Item::Lookaround(_, rule) => contains_non_super_ident(rule, context),
                })
        }
        let context = context
            .filter(|name| contains_non_super_ident(&rule, &name.ident))
            .cloned();
        NonTerminal::Anonymous {
            rule,
            context,
            generics,
        }
    }
}

impl fmt::Display for NonTerminal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NonTerminal::Goal { ident } => {
                write!(f, "Goal({ident})")?;
            }
            NonTerminal::Named { name, generics } => {
                write!(f, "{name}")?;
                if !generics.is_empty() {
                    f.write_str("<")?;
                    for (i, generic) in generics.iter().enumerate() {
                        if i != 0 {
                            f.write_str(", ")?;
                        }
                        write!(f, "{generic}")?;
                    }
                    f.write_str(">")?;
                }
            }
            NonTerminal::Anonymous {
                rule,
                generics,
                context,
            } => {
                match context {
                    Some(context) => write!(f, "{{{rule}}}#{context}")?,
                    None => write!(f, "{{{rule}}}")?,
                }
                if !generics.is_empty() {
                    f.write_str("<")?;
                    for (i, (name, value)) in generics.iter().enumerate() {
                        if i != 0 {
                            f.write_str(", ")?;
                        }
                        write!(f, "{name}={value}")?;
                    }
                    f.write_str(">")?;
                }
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name {
    pub ident: Ident,
    pub index: usize,
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.ident)?;
        if self.index > 0 {
            write!(f, "#{}", self.index)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum Terminal {
    Token(NFA, String),
    EndOfInput(Ident),
}

impl Terminal {
    fn new_token(regex: String) -> Self {
        let nfa = NFA::compiler()
            .configure(NFA::config().shrink(true))
            .build(&regex)
            .expect("Invalid regex");
        if nfa.has_empty() {
            panic!("token {} matches empty string", regex);
        }
        Self::Token(nfa, regex)
    }
}

impl fmt::Display for Terminal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Terminal::Token(_, regex) => write!(f, "/{regex}/"),
            Terminal::EndOfInput(goal) => write!(f, "EoI({goal})"),
        }
    }
}

impl PartialEq for Terminal {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Token(_, this), Self::Token(_, other)) => this.as_str() == other.as_str(),
            (Self::EndOfInput(this), Self::EndOfInput(other)) => this == other,
            _ => false,
        }
    }
}
impl Eq for Terminal {}
impl PartialOrd for Terminal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Terminal {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::Token(_, this), Self::Token(_, other)) => this.as_str().cmp(other.as_str()),
            (Self::EndOfInput(this), Self::EndOfInput(other)) => this.cmp(other),
            (Self::Token(_, _), _) => Ordering::Less,
            (_, Self::Token(_, _)) => Ordering::Greater,
        }
    }
}
impl Hash for Terminal {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            Self::Token(_, regex) => regex.as_str().hash(state),
            Self::EndOfInput(goal) => goal.hash(state),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Production {
    pub alternatives: Vec<Alternative>,
}

impl fmt::Display for Production {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, alternative) in self.alternatives.iter().enumerate() {
            if i != 0 {
                write!(f, " | ")?;
            }
            write!(f, "{alternative}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Alternative {
    pub terms: Vec<Term>,
    pub negative_lookahead: Option<NonTerminal>,
}

impl From<Vec<Term>> for Alternative {
    fn from(terms: Vec<Term>) -> Self {
        Self {
            terms,
            negative_lookahead: None,
        }
    }
}

impl fmt::Display for Alternative {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, term) in self.terms.iter().enumerate() {
            if i != 0 {
                write!(f, " ")?;
            }
            write!(f, "{term}")?;
        }
        if let Some(non_terminal) = &self.negative_lookahead {
            write!(f, " (!>>{non_terminal})")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Term {
    pub kind: TermKind,
    pub silent: bool,
    pub atomic: bool,
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.silent {
            f.write_char('-')?;
        }
        if self.atomic {
            f.write_char('@')?;
        }
        <TermKind as fmt::Display>::fmt(&self.kind, f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TermKind {
    Terminal(Terminal),
    NonTerminal(NonTerminal),
}

impl fmt::Display for TermKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermKind::Terminal(terminal) => write!(f, "{terminal}"),
            TermKind::NonTerminal(non_terminal) => write!(f, "{non_terminal}"),
        }
    }
}
