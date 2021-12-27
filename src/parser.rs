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

fn digits_to_number<I>(num_digits: usize, digits: I) -> u32
where
    I: IntoIterator<Item = char>,
{
    digits.into_iter().enumerate().fold(0, |acc, (i, digit)| {
        acc + match digit {
            '0' => 0,
            '1' => 1,
            '2' => 2,
            '3' => 3,
            '4' => 4,
            '5' => 5,
            '6' => 6,
            '7' => 7,
            '8' => 8,
            '9' => 9,
            _ => unreachable!(),
        } * 10u32.pow((num_digits - i - 1) as u32)
    })
}

fn digits_to_float(digits_before_decimal: Vec<char>, digits_after_decimal: Vec<char>) -> f64 {
    let before_decimal_digit_count = digits_before_decimal.len();
    let after_decimal_digit_count = digits_after_decimal.len();
    let before_decimal = digits_to_number(before_decimal_digit_count, digits_before_decimal) as f64;
    let after_decimal = digits_to_number(after_decimal_digit_count, digits_after_decimal) as f64;
    before_decimal + after_decimal.powi(after_decimal_digit_count as i32 * -1)
}

/// Get a parser that recognizes a single decimal digit.
fn digit<'a>() -> PomParser<'a, char, char> {
    // The : char annotation is needed for the Rust compiler.
    is_a(|c: char| c.is_digit(10))
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
    // Adapted from the EBNF grammar given at the Rust documentation for f64's implementation of FromStr.
    // TODO: Possibly swap out with a more efficient implementation (i.e. the Rust standard library)
    let exp = (one_of("eE") * (symbol(&['+']) | symbol(&['-'])).opt() + digit().repeat(1..)).map(
        |(sgn, digits)| {
            let positive = sgn.map(|op| op == "+").unwrap_or(true);
            let num_digits = digits.len();
            let decimal = digits_to_number(num_digits, digits) as i32;
            if positive {
                decimal
            } else {
                -1 * decimal
            }
        },
    );
    let whole_number = digit()
        .repeat(1..)
        .map(|digits| digits_to_number(digits.len(), digits) as f64);
    let frac_ge_1 = ((digit().repeat(1..) - sym('.')) + digit().repeat(0..))
        .map(|(i, f)| digits_to_float(i, f));
    let frac_lt_1 = ((digit().repeat(0..) - sym('.')) + digit().repeat(1..))
        .map(|(i, f)| digits_to_float(i, f));
    let number =
        ((whole_number | frac_ge_1 | frac_lt_1) + exp.opt()).map(|(base, exp)| match exp {
            Some(exp) => base.powi(exp),
            None => base,
        });
    let inf_or_nan = (symbol(&['i', 'n', 'f']) | symbol(&['N', 'a', 'N'])).map(|lit| {
        if lit == "inf" {
            f64::INFINITY
        } else if lit == "NaN" {
            f64::NAN
        } else {
            unreachable!();
        }
    });
    ((symbol(&['+']) | symbol(&['-'])).opt() + (inf_or_nan | number)).map(|(sgn, value)| {
        let positive = sgn.map(|op| op == "+").unwrap_or(true);
        if positive || value.is_nan() {
            value
        } else if value.is_infinite() {
            f64::NEG_INFINITY
        } else {
            -1.0 * value
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
