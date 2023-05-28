use std::collections::HashMap;

use nom::{
    branch::alt,
    bytes::complete::{escaped, is_not, tag, take_until},
    character::complete::{alphanumeric1, anychar, char, space0, space1},
    combinator::{eof, map, opt, recognize, success, value},
    multi::{count, fold_many0, many0, many1, many1_count, many_m_n, separated_list0},
    sequence::{delimited, preceded, terminated, tuple},
};
use tracing::error;

use crate::util::Interner;

use super::{
    Definition, Expression, Ident, Item, Language, Mark, ParseTree, Quantifier, Rule, Test,
};

type Result<'a, T> = nom::IResult<&'a str, T>;

pub(super) fn parse_grammar(input: &str) -> Language {
    let mut parser = file();
    match parser(input) {
        Ok(("", grammar)) => grammar,
        e => {
            error!(?e, "Failed to parse");
            Language::default()
        }
    }
}

fn file<'a>() -> impl FnMut(&'a str) -> Result<'a, Language> + 'a {
    enum RuleOrTest {
        Rule(Definition),
        Test(Test),
    }
    let file = terminated(
        fold_many0(
            alt((
                map(definition(), RuleOrTest::Rule),
                map(test(), RuleOrTest::Test),
            )),
            || (HashMap::<_, Vec<_>>::new(), HashMap::<_, Vec<_>>::new()),
            |(mut rules, mut tests), rule_or_test| {
                match rule_or_test {
                    RuleOrTest::Rule(rule) => {
                        rules.entry(rule.ident.clone()).or_default().push(rule)
                    }
                    RuleOrTest::Test(test) => {
                        tests.entry(test.ident.clone()).or_default().push(test)
                    }
                }
                (rules, tests)
            },
        ),
        eof,
    );

    map(file, |(rules, tests)| {
        let rules = rules.into_iter().collect();
        let tests = tests.into_iter().collect();
        Language {
            definitions: rules,
            tests,
        }
    })
}

fn definition<'a>() -> impl FnMut(&'a str) -> Result<'a, Definition> + 'a {
    map(
        tuple((
            ws(silent),
            ws(atomic),
            terminated(ws(ident()), tuple((ws(char(':')), opt(empty_lines)))),
            many0(terminated(ws(rule()), empty_lines)),
        )),
        |(silent, atomic, ident, productions)| Definition {
            ident,
            silent,
            atomic,
            rules: productions,
        },
    )
}

fn rule<'a>() -> impl FnMut(&'a str) -> Result<'a, Rule> + 'a {
    map(
        separated_list0(ws(char('|')), expression()),
        |expressions| Rule {
            alternatives: expressions.into_iter().collect(),
        },
    )
}

fn expression<'a>() -> impl FnMut(&'a str) -> Result<'a, Expression> + 'a {
    map(many0(tuple((ws(term()), ws(quantifier)))), |sequence| {
        Expression { sequence }
    })
}

fn term<'a>() -> impl FnMut(&'a str) -> Result<'a, Item> + 'a {
    alt((
        map(tuple((mark, ident())), |(mark, ident)| Item::Ident {
            mark,
            ident,
        }),
        map(quoted_string, Item::String),
        map(regex, Item::Regex),
        map(
            delimited(char('('), move |input| rule()(input), char(')')),
            Item::Group,
        ),
    ))
}

fn silent(input: &str) -> Result<bool> {
    map(ws(opt(char('-'))), |opt| opt.is_some())(input)
}

fn atomic(input: &str) -> Result<bool> {
    map(ws(opt(char('@'))), |opt| opt.is_some())(input)
}

fn mark(input: &str) -> Result<Mark> {
    ws(alt((
        value(Mark::Super, char('$')),
        value(Mark::Sub, char('~')),
        value(Mark::This, success(())),
    )))(input)
}

fn quantifier(input: &str) -> Result<Quantifier> {
    ws(alt((
        value(Quantifier::Any, char('*')),
        value(Quantifier::AtLeastOnce, char('+')),
        value(Quantifier::AtMostOnce, char('?')),
        value(Quantifier::Once, success(())),
    )))(input)
}

fn test<'a>() -> impl FnMut(&'a str) -> Result<'a, Test> + 'a {
    move |input| {
        let (input, hashes) = preceded(space0, many1_count(char('#')))(input)?;
        let (input, ident) = terminated(ws(ident()), nl)(input)?;
        let (input, test) = test_body(hashes)(input)?;
        let (input, _) = ws(count(char('#'), hashes))(input)?;
        let (input, _) = empty_lines(input)?;
        let (input, indent) = space0(input)?;
        let (input, parse_tree) = parse_tree(indent)(input)?;
        let (input, _) = ws(count(char('#'), hashes))(input)?;
        let (input, _) = empty_lines(input)?;
        Ok((
            input,
            Test {
                ident,
                test: test.into(),
                parse_tree,
            },
        ))
    }
}

fn test_body<'a>(hashes: usize) -> impl FnMut(&'a str) -> Result<&'a str> {
    map(
        recognize(many0(terminated(
            alt((recognize(many_m_n(1, hashes - 1, char('#'))), is_not("#\n"))),
            nl,
        ))),
        |s: &str| match s.as_bytes() {
            [.., b'\r', b'\n'] => &s[..s.len() - 2],
            [.., b'\n'] => &s[..s.len() - 1],
            _ => s,
        },
    )
}

fn parse_tree<'a>(indent: &'a str) -> impl FnMut(&'a str) -> Result<'a, ParseTree> + 'a {
    alt((parse_tree_leaf(), parse_tree_node(indent)))
}

fn parse_tree_leaf<'a>() -> impl FnMut(&'a str) -> Result<'a, ParseTree> + 'a {
    map(
        terminated(
            tuple((opt(terminated(ident(), ws(char(':')))), quoted_string)),
            empty_lines,
        ),
        |(ident, data)| ParseTree::Leaf { ident, data },
    )
}

fn parse_tree_node<'a>(indent: &'a str) -> impl FnMut(&'a str) -> Result<'a, ParseTree> + 'a {
    let nodes = move |input| {
        let (input, new_indent) = recognize(tuple((tag(indent), space1)))(input)?;
        let (input, node) = parse_tree(new_indent)(input)?;
        let nodes = vec![node];
        fold_many0(
            preceded(tag(new_indent), parse_tree(new_indent)),
            move || nodes.clone(),
            |mut nodes, node| {
                nodes.push(node);
                nodes
            },
        )(input)
    };
    map(
        tuple((
            terminated(ws(ident()), tuple((char(':'), empty_lines))),
            nodes,
        )),
        |(ident, nodes)| ParseTree::Node { ident, nodes },
    )
}

fn ident<'a>() -> impl FnMut(&'a str) -> Result<'a, Ident> + 'a {
    static IDENT_INTERNER: Interner = Interner::new();
    map(
        recognize(many1(alt((alphanumeric1, tag("_"))))),
        move |ident: &str| Ident(IDENT_INTERNER.intern(ident)),
    )
}

fn quoted_string(input: &str) -> Result<String> {
    let string = |delimiter| {
        map(
            delimited(
                tag(delimiter),
                recognize(take_until(delimiter)),
                tag(delimiter),
            ),
            |s: &str| s.to_owned(),
        )
    };
    alt((string("'"), string("\"")))(input)
}

fn regex(input: &str) -> Result<String> {
    map(
        delimited(char('/'), escaped(is_not("/"), '\\', anychar), char('/')),
        |s: &str| s.to_owned(),
    )(input)
}

fn ws<'a, F, O>(f: F) -> impl FnMut(&'a str) -> Result<'a, O>
where
    F: FnMut(&'a str) -> Result<O>,
{
    delimited(space0, f, space0)
}

fn empty_lines(input: &str) -> Result<&str> {
    recognize(many1(tuple((space0, nl))))(input)
}

fn nl(input: &str) -> Result<&str> {
    recognize(alt((tag("\r\n"), tag("\n"))))(input)
}
