use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt::{self, Write as _},
    hash::Hash,
};

use regex_automata::nfa::thompson::NFA;

use crate::{
    diagnostics::emit,
    language::{Expression, Ident, Item, Language, Mark, Quantifier, Rule},
    Span,
};

pub fn production(language: &Language, non_terminal: &NonTerminalUse) -> Production {
    match non_terminal {
        &NonTerminalUse::Goal { ref ident, span } => {
            let definition = &language.definitions[ident];
            if !definition.generics.is_empty() {
                emit("Goals cannot have generics", vec![(definition.span, None)]);
                return Production {
                    alternatives: vec![],
                };
            }

            Production {
                alternatives: vec![Alternative {
                    span,
                    terms: vec![
                        Term {
                            kind: TermKind::NonTerminal(NonTerminalUse::Named {
                                name: Name {
                                    ident: ident.clone(),
                                    index: 0,
                                },
                                generics: Vec::new(),
                                span,
                            }),
                            silent: definition.silent,
                            atomic: definition.atomic,
                        },
                        Term {
                            kind: TermKind::Terminal(Terminal::EndOfInput(ident.clone(), span)),
                            silent: true,
                            atomic: true,
                        },
                    ],
                    negative_lookahead: None,
                }],
            }
        }
        NonTerminalUse::Named {
            name,
            generics: generic_parameters,
            span,
        } => {
            let definition = &language.definitions[&name.ident];
            if definition.generics.len() != generic_parameters.len() {
                emit(
                    format!(
                        "Expected {} generics, found {}",
                        definition.generics.len(),
                        generic_parameters.len()
                    ),
                    vec![(*span, None)],
                );
                return Production {
                    alternatives: vec![],
                };
            }
            let generics = std::iter::Iterator::zip(
                definition.generics.iter().cloned(),
                generic_parameters.iter().cloned(),
            )
            .collect();
            if definition.rules.is_empty() {
                if name.index > 0 {
                    // ICE
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
                // ICE
                panic!("Index {} out of bounds for {}", name.index, name.ident);
            }
            let mut alternatives: Vec<_> = definition.rules[first..last]
                .iter()
                .flat_map(|rule| lower_rule(language, rule, Some(name), &generics).alternatives)
                .collect();
            if last != definition.rules.len() {
                let span = Span {
                    start: definition.rules[first].span.start,
                    end: definition.rules[last - 1].span.end,
                };
                alternatives.push(Alternative {
                    span,
                    terms: vec![Term {
                        kind: TermKind::NonTerminal(NonTerminalUse::Named {
                            name: Name {
                                ident: name.ident.clone(),
                                index: name.index + 1,
                            },
                            generics: generic_parameters.clone(),
                            span,
                        }),
                        silent: true,
                        atomic: false,
                    }],
                    negative_lookahead: None,
                });
            }
            Production { alternatives }
        }
        NonTerminalUse::Anonymous {
            rule,
            context,
            generics,
        } => {
            if rule.alternatives.len() == 1
                && rule.alternatives.iter().next().unwrap().sequence.len() == 1
            {
                let &(ref item, ref quantifier, span) =
                    &rule.alternatives.iter().next().unwrap().sequence[0];
                let term = lower_term(
                    language,
                    generics,
                    item,
                    Quantifier::Once,
                    span,
                    context.as_ref(),
                );
                let mut alternatives: Vec<Alternative> = Vec::new();
                // Zero times
                if let Quantifier::Any | Quantifier::AtMostOnce = quantifier {
                    alternatives.push(Alternative {
                        span,
                        terms: vec![],
                        negative_lookahead: None,
                    });
                }
                // One time
                if let Quantifier::AtMostOnce | Quantifier::AtLeastOnce | Quantifier::Once =
                    quantifier
                {
                    alternatives.push(Alternative {
                        span,
                        terms: vec![term.clone()],
                        negative_lookahead: None,
                    });
                }
                // Many times
                if let Quantifier::Any | Quantifier::AtLeastOnce = quantifier {
                    alternatives.push(Alternative {
                        span,
                        terms: vec![
                            Term {
                                kind: TermKind::NonTerminal(non_terminal.clone()),
                                silent: true,
                                atomic: false,
                            },
                            term,
                        ],
                        negative_lookahead: None,
                    });
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
    generics: &BTreeMap<Ident, NonTerminalUse>,
) -> Production {
    Production {
        alternatives: rule
            .alternatives
            .iter()
            .map(|expression| {
                let (sequence, lookahead) = match expression.sequence.last() {
                    Some((Item::Lookaround(lookaround_type, rule), quantifier, _)) => {
                        if *quantifier != Quantifier::Once {
                            emit(
                                "Lookaround cannot have a quantifier",
                                vec![(lookaround_type.span, None)],
                            );
                        }
                        let sequence = &expression.sequence[..expression.sequence.len() - 1];
                        if lookaround_type.positive || !lookaround_type.ahead {
                            emit(
                                "Only negative lookahead is supported",
                                vec![(lookaround_type.span, None)],
                            );
                            (sequence, None)
                        } else {
                            (
                                sequence,
                                Some(NonTerminalUse::new_anonymous(
                                    rule.clone(),
                                    current_name,
                                    generics.clone(),
                                )),
                            )
                        }
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
                    span: expression.span,
                    terms,
                    negative_lookahead: lookahead,
                }
            })
            .collect(),
    }
}

fn lower_term(
    language: &Language,
    generics: &BTreeMap<Ident, NonTerminalUse>,
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
            kind: TermKind::NonTerminal(NonTerminalUse::new_anonymous(
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
                    Some(definition) => definition,
                    None => {
                        emit("This identifier is not defined", vec![(span, None)]);
                        return Term {
                            kind: TermKind::NonTerminal(NonTerminalUse::Anonymous {
                                rule: Rule {
                                    span,
                                    alternatives: BTreeSet::new(),
                                },
                                context: None,
                                generics: BTreeMap::new(),
                            }),
                            silent: true,
                            atomic: false,
                        };
                    }
                };
                let generic_parameters = generic_arguments
                    .iter()
                    .map(|arg| {
                        NonTerminalUse::new_anonymous(arg.clone(), current_name, generics.clone())
                    })
                    .collect();
                Term {
                    kind: TermKind::NonTerminal(NonTerminalUse::Named {
                        name,
                        generics: generic_parameters,
                        span,
                    }),
                    silent: definition.silent,
                    atomic: definition.atomic,
                }
            }
        },
        Item::String(data) => Term {
            kind: TermKind::Terminal(Terminal::new_token(regex_syntax::escape(data), span)),
            silent: false,
            atomic: true,
        },
        Item::Regex(regex) => Term {
            kind: TermKind::Terminal(Terminal::new_token(regex.clone(), span)),
            silent: false,
            atomic: true,
        },
        Item::Group(rule) => Term {
            kind: TermKind::NonTerminal(NonTerminalUse::new_anonymous(
                rule.clone(),
                current_name,
                generics.clone(),
            )),
            silent: true,
            atomic: false,
        },
        Item::Lookaround(_, _) => {
            emit(
                "Only negative lookahead is supported and only at the end of an expression",
                vec![(span, None)],
            );
            Term {
                kind: TermKind::NonTerminal(NonTerminalUse::Anonymous {
                    rule: Rule {
                        span,
                        alternatives: BTreeSet::new(),
                    },
                    context: None,
                    generics: BTreeMap::new(),
                }),
                silent: true,
                atomic: false,
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NonTerminalDefinition {
    Goal {
        ident: Ident,
        span: Span,
    },
    Named {
        name: Name,
        generics: Vec<NonTerminalDefinition>,
        span: Span,
    },
    Anonymous {
        rule: Rule,
    },
}

impl NonTerminalDefinition {
    pub fn span(&self) -> Span {
        match self {
            &NonTerminalDefinition::Goal { span, .. } => span,
            &NonTerminalDefinition::Named { span, .. } => span,
            NonTerminalDefinition::Anonymous { rule, .. } => rule.span,
        }
    }
}

impl fmt::Display for NonTerminalDefinition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NonTerminalDefinition::Goal { ident, span: _ } => {
                write!(f, "Goal({ident})")?;
            }
            NonTerminalDefinition::Named {
                name,
                generics,
                span: _,
            } => {
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
            NonTerminalDefinition::Anonymous { rule } => {
                write!(f, "{{{rule}}}")?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NonTerminalUse {
    Goal {
        ident: Ident,
        span: Span,
    },
    Named {
        name: Name,
        generics: Vec<NonTerminalUse>,
        span: Span,
    },
    Anonymous {
        rule: Rule,
        context: Option<Name>,
        generics: BTreeMap<Ident, NonTerminalUse>,
    },
}

impl NonTerminalUse {
    fn new_anonymous(rule: Rule, context: Option<&Name>, generics: BTreeMap<Ident, Self>) -> Self {
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
        Self::Anonymous {
            rule,
            context,
            generics,
        }
    }

    pub fn definition(&self, language: &Language) -> NonTerminalDefinition {
        match self {
            NonTerminalUse::Goal { ident, span } => NonTerminalDefinition::Goal {
                ident: ident.clone(),
                span: *span,
            },
            NonTerminalUse::Named {
                name,
                generics,
                span: _,
            } => NonTerminalDefinition::Named {
                name: name.clone(),
                generics: generics
                    .iter()
                    .map(|generic| generic.definition(language))
                    .collect(),
                span: language.definitions[&name.ident].span,
            },
            NonTerminalUse::Anonymous {
                rule,
                context: _,
                generics: _,
            } => NonTerminalDefinition::Anonymous { rule: rule.clone() },
        }
    }
}

impl fmt::Display for NonTerminalUse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NonTerminalUse::Goal { ident, span: _ } => {
                write!(f, "Goal({ident})")?;
            }
            NonTerminalUse::Named {
                name,
                generics,
                span: _,
            } => {
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
            NonTerminalUse::Anonymous {
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

#[derive(Clone)]
pub enum Terminal {
    Token(NFA, String, Span),
    EndOfInput(Ident, Span),
}

impl Terminal {
    fn new_token(regex: String, span: Span) -> Self {
        let nfa = match NFA::compiler()
            .configure(NFA::config().shrink(true))
            .build(&regex)
        {
            Ok(nfa) => nfa,
            Err(error) => {
                let mut message = error.to_string();
                let mut error: &dyn Error = &error;
                while let Some(source) = error.source() {
                    error = source;
                    write!(message, ": {}", error).unwrap();
                }
                emit("Failed to parse regex", vec![(span, Some(message))]);
                return Self::Token(NFA::never_match(), regex, span);
            }
        };
        if nfa.has_empty() {
            emit("Tokens must not match the empty string", vec![(span, None)]);
        }
        Self::Token(nfa, regex, span)
    }

    pub fn span(&self) -> Span {
        match self {
            Self::Token(_, _, span) => *span,
            Self::EndOfInput(_, span) => *span,
        }
    }
}

impl fmt::Debug for Terminal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Token(_, regex, span) => f.debug_tuple("Token").field(regex).field(span).finish(),
            Self::EndOfInput(ident, span) => f
                .debug_tuple("EndOfInput")
                .field(ident)
                .field(span)
                .finish(),
        }
    }
}

impl fmt::Display for Terminal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Terminal::Token(_, regex, _) => write!(f, "/{regex}/"),
            Terminal::EndOfInput(goal, _) => write!(f, "EoI({goal})"),
        }
    }
}

impl PartialEq for Terminal {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Token(_, this, _), Self::Token(_, other, _)) => this.as_str() == other.as_str(),
            (Self::EndOfInput(this, _), Self::EndOfInput(other, _)) => this == other,
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
            (Self::Token(_, this, _), Self::Token(_, other, _)) => {
                this.as_str().cmp(other.as_str())
            }
            (Self::EndOfInput(this, _), Self::EndOfInput(other, _)) => this.cmp(other),
            (Self::Token(_, _, _), _) => Ordering::Less,
            (_, Self::Token(_, _, _)) => Ordering::Greater,
        }
    }
}
impl Hash for Terminal {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            Self::Token(_, regex, _) => regex.as_str().hash(state),
            Self::EndOfInput(goal, _) => goal.hash(state),
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
    pub span: Span,
    pub terms: Vec<Term>,
    pub negative_lookahead: Option<NonTerminalUse>,
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
    NonTerminal(NonTerminalUse),
}

impl fmt::Display for TermKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermKind::Terminal(terminal) => write!(f, "{terminal}"),
            TermKind::NonTerminal(non_terminal) => write!(f, "{non_terminal}"),
        }
    }
}
