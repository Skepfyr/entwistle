use std::{
    collections::{HashMap, HashSet},
    fmt,
    hash::Hash,
};

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
            Production(
                [vec![
                    Term::NonTerminal(non_terminal.clone()),
                    Term::Terminal(Terminal::EndOfInput(ident.clone())),
                ]]
                .into_iter()
                .collect(),
            ),
        );
        for (index, rule) in definition.rules.iter().enumerate() {
            let name = Name {
                ident: ident.clone(),
                index,
            };
            let mut production = lower_rule(&mut productions, &mut next_anon, rule, &name);
            if name.index < definition.rules.len() - 1 {
                production
                    .0
                    .insert(vec![Term::NonTerminal(NonTerminal::Named {
                        name: Name {
                            ident: ident.clone(),
                            index: index + 1,
                        },
                    })]);
            }
            productions.insert(NonTerminal::Named { name }, production);
        }
    }
    Grammar { productions }
}

fn lower_rule(
    productions: &mut HashMap<NonTerminal, Production>,
    next_anon: &mut impl FnMut() -> NonTerminal,
    rule: &Rule,
    current_name: &Name,
) -> Production {
    Production(
        rule.alternatives
            .iter()
            .map(|expression| {
                expression
                    .sequence
                    .iter()
                    .map(|(term, quantifier)| {
                        lower_term(productions, next_anon, term, *quantifier, current_name)
                    })
                    .collect::<Vec<Term>>()
            })
            .collect(),
    )
}

fn lower_term(
    productions: &mut HashMap<NonTerminal, Production>,
    next_anon: &mut impl FnMut() -> NonTerminal,
    item: &Item,
    quantifier: Quantifier,
    current_name: &Name,
) -> Term {
    if quantifier != Quantifier::Once {
        let non_terminal = next_anon();
        let term = lower_term(productions, next_anon, item, Quantifier::Once, current_name);
        let mut production: HashSet<Vec<Term>> = HashSet::new();
        // Zero times
        if let Quantifier::Any | Quantifier::AtMostOnce = quantifier {
            production.insert(vec![]);
        }
        // One time
        if let Quantifier::AtMostOnce | Quantifier::AtLeastOnce = quantifier {
            production.insert(vec![term.clone()]);
        }
        // Many times
        if let Quantifier::Any | Quantifier::AtLeastOnce = quantifier {
            production.insert(vec![term, Term::NonTerminal(non_terminal.clone())]);
        }
        productions.insert(non_terminal.clone(), Production(production));
        return Term::NonTerminal(non_terminal);
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
            Term::NonTerminal(NonTerminal::Named { name })
        }
        &Item::Char(data) => Term::Terminal(Terminal::Real(data)),
        Item::Group(rule) => {
            let non_terminal = next_anon();
            let production = lower_rule(productions, next_anon, rule, current_name);
            productions.insert(non_terminal.clone(), production);
            Term::NonTerminal(non_terminal)
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Terminal {
    Real(char),
    EndOfInput(Ident),
}

impl fmt::Display for Terminal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Terminal::Real(data) => write!(f, "{data:?}"),
            Terminal::EndOfInput(goal) => write!(f, "EoI({goal})"),
        }
    }
}

#[derive(Debug)]
pub struct Production(pub HashSet<Vec<Term>>);

impl fmt::Display for Production {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, production) in self.0.iter().enumerate() {
            if i != 0 {
                write!(f, " |")?;
            }
            for term in production {
                write!(f, " {term}")?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term {
    Terminal(Terminal),
    NonTerminal(NonTerminal),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Terminal(terminal) => write!(f, "{terminal}"),
            Term::NonTerminal(non_terminal) => write!(f, "{non_terminal}"),
        }
    }
}
