use std::{collections::HashMap, fmt::Write as _, ops::Range};

use chumsky::{
    prelude::*,
    text::{newline, Character},
    Stream,
};

use super::{
    Definition, Expression, Ident, Item, Language, LookaroundType, Mark, ParseTree, QuantifiedItem,
    Quantifier, Rule, Test,
};
use crate::{diagnostics::emit, Db, Span};

pub(super) fn parse_grammar<'db>(db: &'db dyn Db, input: &str) -> Language<'db> {
    let stream = Stream::from_iter(
        Span {
            start: input.len(),
            end: input.len(),
        },
        input.chars().enumerate().map(|(i, c)| {
            (
                c,
                Span {
                    start: i,
                    end: i + 1,
                },
            )
        }),
    );
    match file(db).parse(stream) {
        Ok(grammar) => grammar,
        Err(errors) => {
            for error in errors {
                let mut reason = "Expected one of: ".to_string();
                for (i, expected) in error.expected().enumerate() {
                    if i != 0 {
                        reason.push_str(", ");
                    }
                    match expected {
                        Some(expected) => write!(reason, "{:?}", expected).unwrap(),
                        None => reason.push_str("EOI"),
                    }
                }
                emit("Failed to parse", vec![(error.span(), Some(reason))]);
            }
            Language::new(db, HashMap::new(), Vec::new())
        }
    }
}

type ParseError = Simple<char, Span>;

impl chumsky::Span for Span {
    type Context = ();
    type Offset = usize;

    fn new(_context: Self::Context, range: Range<Self::Offset>) -> Self {
        Self {
            start: range.start,
            end: range.end,
        }
    }

    fn context(&self) -> Self::Context {}

    fn start(&self) -> Self::Offset {
        self.start
    }

    fn end(&self) -> Self::Offset {
        self.end
    }
}

fn file(db: &dyn Db) -> impl Parser<char, Language, Error = ParseError> + '_ {
    enum RuleOrTest<'db> {
        Rule(Definition<'db>),
        Test(Test<'db>),
    }
    choice((
        definition(db).map(RuleOrTest::Rule),
        test(db).map(RuleOrTest::Test),
    ))
    .repeated()
    .map(|items| {
        let (definitions, tests) = items.into_iter().fold(
            (HashMap::new(), Vec::new()),
            |(mut definitions, mut tests), rule_or_test| {
                match rule_or_test {
                    RuleOrTest::Rule(rule) => {
                        if let Some(rule) = definitions.insert(rule.ident, rule) {
                            emit(
                                "Duplicate definition",
                                vec![(
                                    rule.span,
                                    Some(format!("Duplicate definition of {}", rule.ident)),
                                )],
                            );
                        }
                    }
                    RuleOrTest::Test(test) => {
                        tests.push(test);
                    }
                }
                (definitions, tests)
            },
        );
        Language::new(db, definitions, tests)
    })
    .then_ignore(end())
}

fn definition(db: &dyn Db) -> impl Parser<char, Definition, Error = ParseError> + '_ {
    silent()
        .then(atomic())
        .then(
            ident(db)
                .map_with_span(|ident, span| (ident, span))
                .then(generic_params(db).or_not()),
        )
        .then(
            just(':').padded_by(lws()).ignore_then(choice((
                empty_lines().ignore_then(
                    filter(|c: &char| c.is_inline_whitespace())
                        .repeated()
                        .at_least(1)
                        .ignore_then(rule(db))
                        .then_ignore(empty_lines())
                        .repeated(),
                ),
                rule(db).map(|r| vec![r]).then_ignore(empty_lines()),
            ))),
        )
        .map(
            |(((silent, atomic), ((ident, span), generic_params)), productions)| Definition {
                silent,
                atomic,
                ident,
                span,
                generics: generic_params.unwrap_or_default(),
                rules: productions,
            },
        )
}

fn generic_params(db: &dyn Db) -> impl Parser<char, Vec<Ident>, Error = ParseError> + '_ {
    just('<')
        .ignore_then(
            ident(db)
                .padded_by(lws())
                .separated_by(just(','))
                .allow_trailing(),
        )
        .then_ignore(just('>'))
}

fn rule(db: &dyn Db) -> impl Parser<char, Rule<'_>, Error = ParseError> + Clone + '_ {
    recursive(|rule| {
        expression(db, rule)
            .separated_by(just('|').padded_by(lws()))
            .map_with_span(|expressions, span| Rule {
                alternatives: expressions.into_iter().collect(),
                span,
            })
    })
}

fn expression<'db>(
    db: &'db dyn Db,
    rule: impl Parser<char, Rule<'db>, Error = ParseError> + Clone + 'db,
) -> impl Parser<char, Expression<'db>, Error = ParseError> + 'db {
    choice((
        just('(').then(lws()).then(just(')')).to(Vec::new()),
        term(db, rule)
            .then(quantifier())
            .map_with_span(|(item, quantifier), span| QuantifiedItem {
                item,
                quantifier,
                span,
            })
            .separated_by(lws())
            .at_least(1),
    ))
    .map_with_span(|sequence, span| Expression { sequence, span })
}

fn term<'db>(
    db: &'db dyn Db,
    rule: impl Parser<char, Rule<'db>, Error = ParseError> + Clone + 'db,
) -> impl Parser<char, Item<'db>, Error = ParseError> + 'db {
    choice((
        mark()
            .then(ident(db))
            .then(generic_args(rule.clone()).or_not())
            .map(|((mark, ident), generic_args)| Item::Ident {
                mark,
                ident,
                generics: generic_args.unwrap_or_default(),
            }),
        quoted_string().map(Item::String),
        regex().map(Item::Regex),
        just('(')
            .ignore_then(
                lookaround()
                    .padded_by(lws())
                    .then(rule.clone().padded_by(lws())),
            )
            .then_ignore(just(')'))
            .map(|(lookaround_type, rule)| Item::Lookaround(lookaround_type, rule)),
        just('(')
            .ignore_then(rule.padded_by(lws()))
            .then_ignore(just(')'))
            .map(Item::Group),
    ))
}

fn silent() -> impl Parser<char, bool, Error = ParseError> {
    just('-').padded_by(lws()).or_not().map(|opt| opt.is_some())
}

fn atomic() -> impl Parser<char, bool, Error = ParseError> {
    just('@').padded_by(lws()).or_not().map(|opt| opt.is_some())
}

fn mark() -> impl Parser<char, Mark, Error = ParseError> {
    choice((
        just('$').to(Mark::Super),
        just('~').to(Mark::Sub),
        empty().to(Mark::This),
    ))
    .padded_by(lws())
}

fn generic_args<'db>(
    rule: impl Parser<char, Rule<'db>, Error = ParseError>,
) -> impl Parser<char, Vec<Rule<'db>>, Error = ParseError> {
    just('<')
        .ignore_then(
            rule.padded_by(lws())
                .separated_by(just(','))
                .allow_trailing(),
        )
        .then_ignore(just('>'))
}

fn quantifier() -> impl Parser<char, Quantifier, Error = ParseError> {
    choice((
        just('*').to(Quantifier::Any),
        just('+').to(Quantifier::AtLeastOnce),
        just('?').to(Quantifier::AtMostOnce),
        empty().to(Quantifier::Once),
    ))
}

fn lookaround() -> impl Parser<char, LookaroundType, Error = ParseError> {
    just('!')
        .or_not()
        .map(|opt| opt.is_none())
        .then(choice((just(">>").to(true), just("<<").to(false))))
        .map_with_span(|(positive, ahead), span| LookaroundType {
            positive,
            ahead,
            span,
        })
}

fn test(db: &dyn Db) -> impl Parser<char, Test, Error = ParseError> + '_ {
    lws()
        .ignore_then(just('=').repeated().at_least(1).map(|equals| equals.len()))
        .then_with(|equals: usize| {
            rule(db)
                .padded_by(lws())
                .then_ignore(newline())
                .then(test_body(equals).map_with_span(|body, span| (body, span)))
                .then_ignore(just('=').repeated().exactly(equals).padded_by(lws()))
                .then_ignore(empty_lines())
                .then(parse_trees(db))
                .then_ignore(just('=').repeated().exactly(equals).padded_by(lws()))
                .then_ignore(empty_lines())
        })
        .map(|((goal, (test, test_span)), parse_trees)| {
            Test::new(db, goal, test, test_span, parse_trees)
        })
}

fn test_body(equals: usize) -> impl Parser<char, String, Error = ParseError> {
    take_until(lws().then(just('=').repeated().exactly(equals)).rewind())
        .map(|(s, _)| s)
        .collect()
        .map(|mut s: String| {
            match s.as_bytes() {
                [.., b'\r', b'\n'] => s.truncate(s.len() - 2),
                [.., b'\n'] => s.truncate(s.len() - 1),
                _ => {}
            };
            s
        })
}

fn parse_trees(db: &dyn Db) -> impl Parser<char, Vec<ParseTree>, Error = ParseError> + '_ {
    lws()
        .then(
            ident(db)
                .then_ignore(just(':').padded_by(lws()))
                .or_not()
                .then(quoted_string().or_not())
                .then_ignore(empty_lines()),
        )
        .repeated()
        .validate(|lines, span, emit| {
            let mut trees: Vec<(String, Ident, Vec<ParseTree>)> =
                vec![("".into(), Ident::new(db, ""), Vec::new())];
            for (indent, tree_info) in lines {
                while trees
                    .last()
                    .map(|(i, _, _)| i.as_str().len() >= indent.len())
                    .unwrap_or(false)
                    && trees.len() > 1
                {
                    let (old_indent, old_ident, old_nodes) = trees.pop().unwrap();
                    let old_parse_tree = ParseTree::Node {
                        ident: old_ident,
                        nodes: old_nodes,
                    };
                    let (_, _, top_nodes) = trees.last_mut().expect("Above top-level?");
                    if !old_indent.starts_with(&indent) {
                        emit(ParseError::custom(
                            span,
                            "Parse tree indentation must be consistent.",
                        ));
                        return vec![old_parse_tree];
                    }
                    top_nodes.push(old_parse_tree);
                }
                match tree_info {
                    (ident, Some(data)) => {
                        let new_item = ParseTree::Leaf { ident, data };
                        let (_, _, nodes) = trees
                            .last_mut()
                            .expect("There should always be a top-level tree");
                        nodes.push(new_item);
                    }
                    (Some(ident), None) => {
                        trees.push((indent, ident, Vec::new()));
                    }
                    (None, None) => {
                        unreachable!("Empty lines should be ignored")
                    }
                }
            }
            while trees.len() > 1 {
                let (_, ident, nodes) = trees.pop().unwrap();
                trees
                    .last_mut()
                    .unwrap()
                    .2
                    .push(ParseTree::Node { ident, nodes });
            }
            match trees.pop() {
                Some((_, _, nodes)) => nodes,
                None => {
                    emit(ParseError::custom(span, "No parse tree found."));
                    vec![]
                }
            }
        })
}

fn ident(db: &dyn Db) -> impl Parser<char, Ident, Error = ParseError> + '_ {
    chumsky::text::ident()
        .map(move |ident: String| Ident::new(db, ident))
        .labelled("ident")
}

fn quoted_string() -> impl Parser<char, String, Error = ParseError> {
    let string = |delimiter| {
        just(delimiter)
            .ignore_then(none_of([delimiter, '\n']).repeated().collect())
            .then_ignore(just(delimiter))
    };
    string('"').or(string('\''))
}

fn regex() -> impl Parser<char, String, Error = ParseError> {
    just('/')
        .ignore_then(
            none_of("\\/")
                .map(|c| vec![c])
                .or(just('\\').ignore_then(choice((
                    just('/').to(vec!['/']),
                    none_of("/").map(|c| vec!['\\', c]),
                ))))
                .repeated()
                .flatten()
                .collect(),
        )
        .then_ignore(just('/'))
}

fn empty_lines() -> impl Parser<char, (), Error = ParseError> {
    lws()
        .then(line_comment().or_not())
        .then(newline())
        .ignored()
        .repeated()
        .at_least(1)
        .collect()
}

fn line_comment() -> impl Parser<char, (), Error = ParseError> {
    just('#')
        .chain(filter(|c: &char| !c.is_control()).repeated())
        .ignored()
}

fn lws() -> impl Parser<char, String, Error = ParseError> + Clone {
    filter(|c: &char| c.is_inline_whitespace())
        .repeated()
        .collect()
}
