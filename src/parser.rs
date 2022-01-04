use pom::parser::{Parser as PomParser, *};

use std::iter::once;

use crate::ast::Identifier;

/// Type alias for a [`pom::parser::Parser`] that parses streams of [`char`]aracters and outputs
/// [`String`]s.
///
/// The lifetime parameter `'a` is the lifetime of the data source being parsed.
pub type Parser<'a> = pom::parser::Parser<'a, char, String>;

/// Get a parser that parses the start of a single-line comment: `//`.
fn line_start<'a>() -> PomParser<'a, char, ()> {
    // TODO: Is there a way to convert an &str to an &[char] so that I can do seq("//")?
    seq(&['/', '/']).discard()
}

/// Get a parser that parses the start of a block comment: `/*`.
fn block_start<'a>() -> PomParser<'a, char, ()> {
    seq(&['/', '*']).discard()
}

/// Get a parser that parses the end of a block comment: `*/`.
fn block_end<'a>() -> PomParser<'a, char, ()> {
    seq(&['*', '/']).discard()
}

/// Get a parser than can parse nested block comments.
fn block<'a>() -> PomParser<'a, char, ()> {
    block_start() * any().repeat(0..) * call(block).opt() * any().repeat(0..) * block_end()
}

/// Get a function that takes a parser and returns a parser that recognizes `open` followed by the
/// parser followed by `close`.
fn between<'a>(open: Parser<'a>, close: Parser<'a>) -> impl FnOnce(Parser<'a>) -> Parser<'a> {
    |p| (open * p) - close
}

/// The space consumer parser. This parser dictates what's ignored while parsing source code.
/// "Space" is anything considered whitespace by [`char::is_whitespace`]. This parser also ignores
/// single line comments (anything starting with `//` and ending at the end of a line) and block
/// comments (anything in between `/*` and `*/`). Block comments can be nested.
pub fn sc<'a>() -> PomParser<'a, char, ()> {
    let sp = is_a(char::is_whitespace).discard();
    let line = (line_start() * any().repeat(0..) * sym('\r').opt() * sym('\n')).discard();
    let block = block();
    (sp | line | block).repeat(0..).discard()
}

/// Get a parser that lexes input based on the given parser and what is determined to be whitespace
/// by the [`sc`] parser. The returned lexeme is one that would be recognized by the given parser.
pub fn lexeme<'a, T: 'a>(p: PomParser<'a, char, T>) -> PomParser<'a, char, T> {
    p - sc()
}

/// Get a parser that parses the given verbatim string, ignoring any following whitespace.
pub fn symbol<'a, 'b: 'a>(tag: &'b [char]) -> Parser<'a> {
    lexeme(seq(tag)).map(|o| o.iter().collect())
}

/// Get a parser that parses a parenthesized parser. That is, a parser that wraps the given parser
/// to expect an opening parenthesis, a string recognized by the given parser, then a closing
/// parenthesis.
pub fn parens(p: Parser) -> Parser {
    between(symbol(&['(']), symbol(&[')']))(p)
}

/// Get a parser that parses a bracketed parser. That is, a parser that wraps the given parser to
/// expect an opening curly bracket ({), a string recognized by the given parser, then a closing
/// curly bracket (}).
pub fn braces(p: Parser) -> Parser {
    between(symbol(&['{']), symbol(&['}']))(p)
}

/// Get a parser that recognized the semicolon lexeme, i.e. `;`.
pub fn semi<'a>() -> Parser<'a> {
    symbol(&[';'])
}

/// Get a parser that parses identifiers: bare words that are not keywords or string literals.
pub fn identifier<'a>() -> PomParser<'a, char, Identifier> {
    lexeme(
        (is_a(char::is_alphabetic) + is_a(char::is_alphanumeric).repeat(0..))
            .map(|(fst, rest)| once(fst).chain(rest.into_iter()).collect()),
    )
}

/// Get a parser that parses string literals.
pub fn string_lit<'a>() -> Parser<'a> {
    todo!("Parse string literals (including escape sequences!)");
}

/// Get a parser that parses number literals.
pub fn number<'a>() -> PomParser<'a, char, f64> {
    PomParser::new(move |input: &'a [char], start: usize| {
        match fast_float::parse_partial::<f64, _>(String::from_iter(input.into_iter())) {
            Ok((num, num_digits)) => Ok((num, start + num_digits)),
            Err(e) => Err(pom::Error::Custom {
                message: e.to_string(),
                position: start,
                inner: None,
            }),
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn str_slice_to_vec(str_slice: &str) -> Vec<char> {
        str_slice.chars().collect::<Vec<char>>()
    }

    #[test]
    fn parse_ident() {
        let input = &*str_slice_to_vec("num1   ");
        let identifier = identifier();
        assert_eq!(identifier.parse(input), Ok("num1".into()));
    }

    #[test]
    fn parse_parens() {
        let input = &*str_slice_to_vec("( num1 )  ");
        let parens = parens(identifier());
        assert_eq!(parens.parse(input), Ok("num1".into()));
    }

    #[test]
    fn parse_numbers() {
        // I want to keep each tuple that is being passed to HashMap::from on its own line for
        // readability, but rustfmt seems to want to condense this all onto one line, so this
        // #[rustfmt::skip] annotation is needed.
        #[rustfmt::skip]
        let expected = HashMap::from([
            ("1   ", 1.0),
            ("-12   ", -12.0)
        ]);
        for (num, expected) in expected {
            let input = &*str_slice_to_vec(num);
            assert_eq!(number().parse(input), Ok(expected));
        }
    }
}
