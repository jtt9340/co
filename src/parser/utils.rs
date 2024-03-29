//! Helper functions for parsing.

use pom::parser::*;

use crate::ast::Expr;

use super::sc;

/// Get a function that takes a parser and returns a parser that recognizes `open` followed by the
/// parser followed by `close`.
pub(in crate::parser) fn between<'a, I, O, U, V>(
    open: Parser<'a, I, U>,
    close: Parser<'a, I, V>,
) -> impl FnOnce(Parser<'a, I, O>) -> Parser<'a, I, O>
where
    O: 'a,
    U: 'a,
    V: 'a,
{
    |p| (open * p) - close
}

/// Apply parser `p` *zero* or more times until parser `end` succeeds or parser `p` fails, whichever
/// occurs first. If `p` fails, returns the error that `p` gives, otherwise returns a 2-tuple where
/// the the first item in the tuple is the list of values returned by `p`, and the second item in
/// the tuple is the token consumed by `end`.
pub(in crate::parser) fn many_until<'a, I, U, O>(
    p: Parser<'a, I, O>,
    end: Parser<'a, I, U>,
) -> Parser<'a, I, (Vec<O>, U)>
where
    O: 'a,
    U: 'a,
{
    Parser::new(move |input: &'a [I], start: usize| {
        let mut items = Vec::new();
        let mut pos = start;

        let end_result = loop {
            if let Ok((end_output, end_pos)) = (end.method)(input, pos) {
                pos = end_pos;
                break end_output;
            }

            match (p.method)(input, pos) {
                Ok((item, item_pos)) => {
                    items.push(item);
                    pos = item_pos;
                }
                Err(e) => return Err(e),
            }
        };

        Ok(((items, end_result), pos))
    })
}

/// Get a parser that lexes input based on the given parser and what is determined to be whitespace
/// by the [`sc`] parser. The returned lexeme is one that would be recognized by the given parser.
pub(in crate::parser) fn lexeme<'a, T: 'a>(p: Parser<'a, char, T>) -> Parser<'a, char, T> {
    p - sc()
}

/// Get a parser that parses the given verbatim string, ignoring any following whitespace.
pub(in crate::parser) fn symbol(s: &str) -> Parser<char, &str> {
    lexeme(tag(s))
}

/// Get a parser that parses a parenthesized parser. That is, a parser that wraps the given parser
/// to expect an opening parenthesis, a string recognized by the given parser, then a closing
/// parenthesis.
pub(in crate::parser) fn parens<'a, O>(p: Parser<'a, char, O>) -> Parser<'a, char, O>
where
    O: 'a,
{
    between(lexeme(sym('(')), lexeme(sym(')')))(p)
}

/// Get a parser that parses a bracketed parser. That is, a parser that wraps the given parser to
/// expect an opening curly bracket (`{`), a string recognized by the given parser, then a closing
/// curly bracket (`}`).
pub(in crate::parser) fn braces<'a, O>(p: Parser<'a, char, O>) -> Parser<'a, char, O>
where
    O: 'a,
{
    between(lexeme(sym('{')), lexeme(sym('}')))(p)
}

pub(in crate::parser) fn args_lists_to_expr(
    callee: Expr,
    args_lists: impl IntoIterator<Item = Vec<Expr>>,
) -> Expr {
    let mut iter = args_lists.into_iter();
    match iter.next() {
        Some(args_list) => args_lists_to_expr(Expr::Call(Box::new(callee), args_list), iter),
        None => callee,
    }
}
