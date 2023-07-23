use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
    fmt::{self, Write as _},
    hash::Hash,
};

use regex_automata::nfa::thompson::NFA;

use crate::language::{Definition, Ident, Item, Language, Mark, Quantifier, Rule};

#[derive(Debug)]
pub struct Grammar {
    pub productions: HashMap<NonTerminal, Production>,
}

impl fmt::Display for Grammar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (nt, production) in &self.productions {
            writeln!(f, "{nt}: {production}")?;
        }
        Ok(())
    }
}

pub fn lower(language: &Language) -> Grammar {
    let mut productions = HashMap::new();
    let mut next_anon = {
        let mut next_index = 0;
        move || {
            let index = next_index;
            next_index += 1;
            NonTerminal::Anonymous { index }
        }
    };
    for (ident, definitions) in &language.definitions {
        let definition: &Definition = match definitions.as_slice() {
            [definition] => definition,
            _ => panic!("Should have exactly one rule"),
        };
        let non_terminal = NonTerminal::Named {
            name: Name {
                ident: ident.clone(),
                index: 0,
            },
        };
        productions.insert(
            NonTerminal::Goal {
                ident: ident.clone(),
            },
            Production {
                alternatives: [vec![
                    Term {
                        kind: TermKind::NonTerminal(non_terminal.clone()),
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
            },
        );
        for (index, rule) in definition.rules.iter().enumerate() {
            let name = Name {
                ident: ident.clone(),
                index,
            };
            let mut production =
                lower_rule(language, &mut productions, &mut next_anon, rule, &name);
            if name.index < definition.rules.len() - 1 {
                production.alternatives.insert(
                    vec![Term {
                        kind: TermKind::NonTerminal(NonTerminal::Named {
                            name: Name {
                                ident: ident.clone(),
                                index: index + 1,
                            },
                        }),
                        silent: true,
                        atomic: false,
                    }]
                    .into(),
                );
            }
            productions.insert(NonTerminal::Named { name }, production);
        }
    }
    Grammar { productions }
}

fn lower_rule(
    language: &Language,
    productions: &mut HashMap<NonTerminal, Production>,
    next_anon: &mut impl FnMut() -> NonTerminal,
    rule: &Rule,
    current_name: &Name,
) -> Production {
    Production {
        alternatives: rule
            .alternatives
            .iter()
            .map(|expression| {
                let (sequence, lookahead) = match expression.sequence.last() {
                    Some((Item::Lookaround(lookaround_type, rule), Quantifier::Once)) => {
                        if lookaround_type.positive || !lookaround_type.ahead {
                            panic!("Only negative lookahead is supported");
                        }
                        let production =
                            lower_rule(language, productions, next_anon, rule, current_name);
                        let non_terminal = next_anon();
                        productions.insert(non_terminal.clone(), production);
                        (
                            &expression.sequence[..expression.sequence.len() - 1],
                            Some(non_terminal),
                        )
                    }
                    Some((Item::Lookaround(_, _), _)) => {
                        panic!("Lookaround cannot have a quantifier")
                    }
                    _ => (&expression.sequence[..], None),
                };
                let terms = sequence
                    .iter()
                    .map(|(term, quantifier)| {
                        lower_term(
                            language,
                            productions,
                            next_anon,
                            term,
                            *quantifier,
                            current_name,
                        )
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
    productions: &mut HashMap<NonTerminal, Production>,
    next_anon: &mut impl FnMut() -> NonTerminal,
    item: &Item,
    quantifier: Quantifier,
    current_name: &Name,
) -> Term {
    if quantifier != Quantifier::Once {
        let non_terminal = next_anon();
        let term = lower_term(
            language,
            productions,
            next_anon,
            item,
            Quantifier::Once,
            current_name,
        );
        let mut alternatives: HashSet<Alternative> = HashSet::new();
        // Zero times
        if let Quantifier::Any | Quantifier::AtMostOnce = quantifier {
            alternatives.insert(vec![].into());
        }
        // One time
        if let Quantifier::AtMostOnce | Quantifier::AtLeastOnce = quantifier {
            alternatives.insert(vec![term.clone()].into());
        }
        // Many times
        if let Quantifier::Any | Quantifier::AtLeastOnce = quantifier {
            alternatives.insert(
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
        productions.insert(non_terminal.clone(), Production { alternatives });
        return Term {
            kind: TermKind::NonTerminal(non_terminal),
            silent: true,
            atomic: false,
        };
    }

    match item {
        Item::Ident { mark, ident } => {
            let name = if ident == &current_name.ident {
                Name {
                    ident: current_name.ident.clone(),
                    index: match mark {
                        Mark::Super => 0,
                        Mark::This => current_name.index,
                        Mark::Sub => current_name.index + 1,
                    },
                }
            } else {
                Name {
                    ident: ident.clone(),
                    index: 0,
                }
            };
            let definition = &language.definitions[ident][0];
            Term {
                kind: TermKind::NonTerminal(NonTerminal::Named { name }),
                silent: definition.silent,
                atomic: definition.atomic,
            }
        }
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
        Item::Group(rule) => {
            let non_terminal = next_anon();
            let production = lower_rule(language, productions, next_anon, rule, current_name);
            productions.insert(non_terminal.clone(), production);
            Term {
                kind: TermKind::NonTerminal(non_terminal),
                silent: true,
                atomic: false,
            }
        }
        Item::Lookaround(_, _) => {
            panic!("Only negative lookahead is supported at the end of an expression")
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NonTerminal {
    Goal { ident: Ident },
    Named { name: Name },
    Anonymous { index: u32 },
}

impl fmt::Display for NonTerminal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NonTerminal::Goal { ident } => {
                write!(f, "Goal({ident})")
            }
            NonTerminal::Named { name } => {
                write!(f, "{name}")
            }
            NonTerminal::Anonymous { index } => write!(f, "#{index}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name {
    pub ident: Ident,
    pub index: usize,
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}#{}", self.ident, self.index)
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

#[derive(Debug)]
pub struct Production {
    pub alternatives: HashSet<Alternative>,
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
