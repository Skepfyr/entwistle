use std::ops::Range;

use chumsky::{
    prelude::*,
    text::{newline, Character},
    Stream,
};
use tracing::error;

use crate::{util::Interner, Span};

use super::{
    Definition, Expression, Ident, Item, Language, LookaroundType, Mark, ParseTree, Quantifier,
    Rule, Test,
};

pub(super) fn parse_grammar(input: &str) -> Language {
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
    match file().parse(stream) {
        Ok(grammar) => grammar,
        Err(errors) => {
            for error in errors {
                error!(?error, "Failed to parse");
            }
            Language::default()
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

fn file() -> impl Parser<char, Language, Error = ParseError> {
    enum RuleOrTest {
        Rule(Definition),
        Test(Test),
    }
    choice((
        definition().map(RuleOrTest::Rule),
        test().map(RuleOrTest::Test),
    ))
    .repeated()
    .map(|items| {
        items
            .into_iter()
            .fold(Language::default(), |mut language, rule_or_test| {
                match rule_or_test {
                    RuleOrTest::Rule(rule) => language
                        .definitions
                        .entry(rule.ident.clone())
                        .or_default()
                        .push(rule),
                    RuleOrTest::Test(test) => language
                        .tests
                        .entry(test.ident.clone())
                        .or_default()
                        .push(test),
                }
                language
            })
    })
    .then_ignore(end())
}

fn definition() -> impl Parser<char, Definition, Error = ParseError> {
    silent()
        .then(atomic())
        .then(
            ident()
                .map_with_span(|ident, span| (ident, span))
                .then(generic_params().or_not()),
        )
        .then(
            just(':').padded_by(lws()).ignore_then(choice((
                empty_lines().ignore_then(
                    filter(|c: &char| c.is_inline_whitespace())
                        .repeated()
                        .at_least(1)
                        .ignore_then(rule())
                        .then_ignore(empty_lines())
                        .repeated(),
                ),
                rule().map(|r| vec![r]).then_ignore(empty_lines()),
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

fn generic_params() -> impl Parser<char, Vec<Ident>, Error = ParseError> {
    just('<')
        .ignore_then(
            ident()
                .padded_by(lws())
                .separated_by(just(','))
                .allow_trailing(),
        )
        .then_ignore(just('>'))
}

fn rule() -> impl Parser<char, Rule, Error = ParseError> + Clone {
    recursive(|rule| {
        expression(rule)
            .separated_by(just('|').padded_by(lws()))
            .map_with_span(|expressions, span| Rule {
                alternatives: expressions.into_iter().collect(),
                span,
            })
    })
}

fn expression(
    rule: impl Parser<char, Rule, Error = ParseError> + Clone,
) -> impl Parser<char, Expression, Error = ParseError> {
    choice((
        term(rule)
            .then(quantifier())
            .padded_by(lws())
            .map_with_span(|(item, quantifier), span| (item, quantifier, span))
            .repeated()
            .at_least(1),
        just("()").to(Vec::new()),
    ))
    .map_with_span(|sequence, span| Expression { sequence, span })
}

fn term(
    rule: impl Parser<char, Rule, Error = ParseError> + Clone,
) -> impl Parser<char, Item, Error = ParseError> {
    choice((
        mark()
            .then(ident())
            .then(generic_args(rule.clone()).or_not())
            .map(|((mark, ident), generic_args)| Item::Ident {
                mark,
                ident,
                generics: generic_args.unwrap_or_default(),
            }),
        quoted_string().map(Item::String),
        regex().map(Item::Regex),
        just('(')
            .ignore_then(lookaround().then(rule.clone()))
            .then_ignore(just(')'))
            .map(|(lookaround_type, rule)| Item::Lookaround(lookaround_type, rule)),
        just('(')
            .ignore_then(rule)
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

fn generic_args(
    rule: impl Parser<char, Rule, Error = ParseError>,
) -> impl Parser<char, Vec<Rule>, Error = ParseError> {
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
        .map(|(positive, ahead)| LookaroundType { positive, ahead })
}

fn test() -> impl Parser<char, Test, Error = ParseError> {
    lws()
        .ignore_then(just('=').repeated().at_least(1).map(|equals| equals.len()))
        .then_with(|equals: usize| {
            ident()
                .map_with_span(|ident, span| (ident, span))
                .padded_by(lws())
                .then_ignore(newline())
                .then(test_body(equals))
                .then_ignore(just('=').repeated().exactly(equals).padded_by(lws()))
                .then_ignore(empty_lines())
                .then(parse_tree())
                .then_ignore(just('=').repeated().exactly(equals).padded_by(lws()))
                .then_ignore(empty_lines())
        })
        .map(|(((ident, span), test), parse_tree)| Test {
            ident,
            span,
            test: test.into(),
            parse_tree,
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

fn parse_tree() -> impl Parser<char, ParseTree, Error = ParseError> {
    lws()
        .then(
            ident()
                .then_ignore(just(':').padded_by(lws()))
                .or_not()
                .then(quoted_string().or_not())
                .then_ignore(empty_lines()),
        )
        .repeated()
        .validate(|lines, span, emit| {
            let mut trees: Vec<(String, Ident, Vec<ParseTree>)> = Vec::new();
            for (indent, tree_info) in lines {
                while trees
                    .last()
                    .map(|(i, _, _)| i.as_str().len() >= indent.len())
                    .unwrap_or(false)
                {
                    let (old_indent, old_ident, old_nodes) = trees.pop().unwrap();
                    let old_parse_tree = ParseTree::Node {
                        ident: old_ident,
                        nodes: old_nodes,
                    };
                    let Some((_, _, top_nodes)) = trees.last_mut() else {
                        emit(ParseError::custom(span, "Only one top level parse tree is allowed."));
                        return old_parse_tree;
                    };
                    if !old_indent.starts_with(&indent) {
                        emit(ParseError::custom(
                            span,
                            "Parse tree indentation must be consistent.",
                        ));
                        return old_parse_tree;
                    }
                    top_nodes.push(old_parse_tree);
                }
                match tree_info {
                    (ident, Some(data)) => {
                        let new_item = ParseTree::Leaf { ident, data };
                        match trees.last_mut() {
                            Some((_, _, nodes)) => nodes.push(new_item),
                            None => return new_item,
                        }
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
                Some((_, ident, nodes)) => ParseTree::Node { ident, nodes },
                None => {
                    emit(ParseError::custom(span, "No parse tree found."));
                    ParseTree::Leaf {
                        ident: None,
                        data: String::new(),
                    }
                }
            }
        })
}

fn ident() -> impl Parser<char, Ident, Error = ParseError> {
    static IDENT_INTERNER: Interner = Interner::new();
    chumsky::text::ident()
        .map(move |ident: String| Ident(IDENT_INTERNER.intern(&ident)))
        .labelled("ident")
}

fn quoted_string() -> impl Parser<char, String, Error = ParseError> {
    let string = |delimiter| {
        just(delimiter)
            .ignore_then(none_of(delimiter).repeated().collect())
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
