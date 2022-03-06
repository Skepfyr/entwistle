use im::OrdMap;
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take_until},
    character::complete::{alphanumeric1, char, space0, space1},
    combinator::{eof, map, opt, recognize, success, value},
    error::{Error, ErrorKind},
    multi::{count, fold_many0, many0, many1, many1_count, many_m_n, separated_list0},
    sequence::{delimited, preceded, terminated, tuple},
};
use regex::Regex;

use super::{
    Expression, Grammar, Ident, Language, Mark, ParseTree, Production, Quantifier, Rule, Term, Test,
};

type Result<'a, T> = nom::IResult<&'a str, T>;

pub(super) fn parse_grammar(db: &dyn Language) -> Grammar {
    let input = match db.file(db.main()) {
        Ok(input) => input,
        Err(_) => return Grammar::default(),
    };
    let mut parser = file(db);
    match parser(&input) {
        Ok(("", grammar)) => grammar,
        _ => Grammar::default(),
    }
}

fn file<'a>(db: &'a dyn Language) -> impl FnMut(&'a str) -> Result<'a, Grammar> + 'a {
    enum RuleOrTest {
        Rule(Rule),
        Test(Test),
    }
    let file = terminated(
        fold_many0(
            alt((
                map(rule(db), RuleOrTest::Rule),
                map(test(db), RuleOrTest::Test),
            )),
            || (OrdMap::<_, Vec<_>>::new(), OrdMap::<_, Vec<_>>::new()),
            |(mut rules, mut tests), rule_or_test| {
                match rule_or_test {
                    RuleOrTest::Rule(rule) => rules.entry(rule.ident).or_default().push(rule),
                    RuleOrTest::Test(test) => tests.entry(test.ident).or_default().push(test),
                }
                (rules, tests)
            },
        ),
        eof,
    );

    map(file, |(rules, tests)| {
        let rules = rules.into_iter().collect();
        let tests = tests.into_iter().collect();
        Grammar { rules, tests }
    })
}

fn rule<'a>(db: &'a dyn Language) -> impl FnMut(&'a str) -> Result<'a, Rule> + 'a {
    map(
        tuple((
            ws(silent),
            ws(atomic),
            terminated(ws(ident(db)), tuple((ws(char(':')), opt(empty_lines)))),
            many0(terminated(ws(production(db)), empty_lines)),
        )),
        |(silent, atomic, ident, productions)| Rule {
            ident,
            silent,
            atomic,
            productions,
        },
    )
}

fn production<'a>(db: &'a dyn Language) -> impl FnMut(&'a str) -> Result<'a, Production> + 'a {
    map(
        separated_list0(ws(char('|')), expression(db)),
        |expressions| Production {
            alternatives: expressions.into_iter().collect(),
        },
    )
}

fn expression<'a>(db: &'a dyn Language) -> impl FnMut(&'a str) -> Result<'a, Expression> + 'a {
    map(many0(tuple((ws(term(db)), ws(quantifier)))), |sequence| {
        Expression { sequence }
    })
}

fn term<'a>(db: &'a dyn Language) -> impl FnMut(&'a str) -> Result<'a, Term> + 'a {
    alt((
        map(tuple((mark, ident(db))), |(mark, ident)| Term::Ident {
            mark,
            ident,
        }),
        map(quoted_string, Term::String),
        map(regex, Term::Regex),
        map(
            delimited(char('('), move |input| production(db)(input), char(')')),
            Term::Group,
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

fn test<'a>(db: &'a dyn Language) -> impl FnMut(&'a str) -> Result<'a, Test> + 'a {
    move |input| {
        let (input, hashes) = preceded(space0, many1_count(char('#')))(input)?;
        let (input, ident) = terminated(ws(ident(db)), nl)(input)?;
        let (input, test) = test_body(hashes)(input)?;
        let (input, _) = ws(count(char('#'), hashes))(input)?;
        let (input, _) = empty_lines(input)?;
        let (input, indent) = space0(input)?;
        let (input, parse_tree) = parse_tree(db, indent)(input)?;
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

fn parse_tree<'a>(
    db: &'a dyn Language,
    indent: &'a str,
) -> impl FnMut(&'a str) -> Result<'a, ParseTree> + 'a {
    alt((parse_tree_leaf(db), parse_tree_node(db, indent)))
}

fn parse_tree_leaf<'a>(db: &'a dyn Language) -> impl FnMut(&'a str) -> Result<'a, ParseTree> + 'a {
    map(
        terminated(
            tuple((opt(terminated(ident(db), ws(char(':')))), quoted_string)),
            empty_lines,
        ),
        |(ident, data)| ParseTree::Leaf {
            ident,
            data: data.into(),
        },
    )
}

fn parse_tree_node<'a>(
    db: &'a dyn Language,
    indent: &'a str,
) -> impl FnMut(&'a str) -> Result<'a, ParseTree> + 'a {
    let nodes = move |input| {
        let (input, new_indent) = recognize(tuple((tag(indent), space1)))(input)?;
        let (input, node) = parse_tree(db, new_indent)(input)?;
        let nodes = vec![node];
        fold_many0(
            preceded(tag(new_indent), parse_tree(db, new_indent)),
            move || nodes.clone(),
            |mut nodes, node| {
                nodes.push(node);
                nodes
            },
        )(input)
    };
    map(
        tuple((
            terminated(ws(ident(db)), tuple((char(':'), empty_lines))),
            nodes,
        )),
        |(ident, nodes)| ParseTree::Node {
            ident,
            nodes: nodes.into(),
        },
    )
}

fn ident<'a>(db: &'a dyn Language) -> impl FnMut(&'a str) -> Result<'a, Ident> + 'a {
    map(
        recognize(many1(alt((alphanumeric1, tag("_"))))),
        move |ident: &str| db.intern_ident(ident.to_owned()),
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

fn regex(first_input: &str) -> Result<Regex> {
    let (input, delimiter) = recognize(many1(char('/')))(first_input)?;
    let (input, regex) = recognize(take_until(delimiter))(input)?;
    let (input, _) = tag(delimiter)(input)?;
    Ok((
        input,
        Regex::new(regex).map_err(|_| {
            nom::Err::Error(Error {
                input: first_input,
                code: ErrorKind::MapRes,
            })
        })?,
    ))
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
