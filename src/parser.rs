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
    let skip_comment_char = (!block_end() * any()).discard();
    let comment_content = (call(block) | skip_comment_char).repeat(0..).discard();
    (block_start() * comment_content) - block_end()
}

/// Get a function that takes a parser and returns a parser that recognizes `open` followed by the
/// parser followed by `close`.
fn between<'a>(open: Parser<'a>, close: Parser<'a>) -> impl FnOnce(Parser<'a>) -> Parser<'a> {
    |p| (open * p) - close
}

/// Apply parser `p` *zero* or more times until parser `end` succeeds or parser `p` fails, whichever
/// occurs first. If `p` fails, returns the error that `p` gives, otherwise returns a 2-tuple where
/// the the first item in the tuple is the list of values returned by `p`, and the second item in
/// the tuple is the token consumed by `end`.
fn many_until<'a, I, U, O>(
    p: PomParser<'a, I, O>,
    end: PomParser<'a, I, U>,
) -> PomParser<'a, I, (Vec<O>, U)>
where
    O: 'a,
    U: 'a,
{
    PomParser::new(move |input: &'a [I], start: usize| {
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

/// The space consumer parser. This parser dictates what's ignored while parsing source code.
/// "Space" is anything considered whitespace by [`char::is_whitespace`]. This parser also ignores
/// single line comments (anything starting with `//` and ending at the end of a line) and block
/// comments (anything in between `/*` and `*/`). Block comments can be nested.
pub fn sc<'a>() -> PomParser<'a, char, ()> {
    let sp = is_a(char::is_whitespace).discard();
    let line = (line_start() * many_until(any(), sym('\r').opt() * sym('\n'))).discard();
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
    let charesc = one_of("abfnrtv\\\"\'&").map(|esc| match esc {
        'a' => Some('\x07'),
        'b' => Some('\x08'),
        'f' => Some('\x0C'),
        'n' => Some('\n'),
        'r' => Some('\r'),
        't' => Some('\t'),
        'v' => Some('\x0B'),
        '\\' => Some('\\'),
        '\"' => Some('\"'),
        '\'' => Some('\''),
        '&' => None,
        _ => panic!("Unrecognized escape sequence \\{}", esc),
    });
    // If I pass char::is_ascii_uppercase to is_a, Rust thinks is_a should return a Parser<'_, &char, &char>
    // because char::is_ascii_uppercase takes a character by reference. I also need the type annotation
    // on the closure because Rust cannot figure it out itself.
    let cntrl = (is_a(|c: char| c.is_ascii_uppercase()) | one_of("@[\\]^_")).map(|ctl| match ctl {
        'A' => Some('\x01'),
        'B' => Some('\x02'),
        'C' => Some('\x03'),
        'D' => Some('\x04'),
        'E' => Some('\x05'),
        'F' => Some('\x06'),
        'G' => Some('\x07'),
        'H' => Some('\x08'),
        'I' => Some('\x09'),
        'J' => Some('\x0A'),
        'K' => Some('\x0B'),
        'L' => Some('\x0C'),
        'M' => Some('\x0D'),
        'N' => Some('\x0E'),
        'O' => Some('\x0F'),
        'P' => Some('\x10'),
        'Q' => Some('\x11'),
        'R' => Some('\x12'),
        'S' => Some('\x13'),
        'T' => Some('\x14'),
        'U' => Some('\x15'),
        'V' => Some('\x16'),
        'W' => Some('\x17'),
        'X' => Some('\x18'),
        'Y' => Some('\x19'),
        'Z' => Some('\x1A'),
        '@' => Some('\0'),
        '[' => Some('\x1B'),
        '\\' => Some('\x1C'),
        ']' => Some('\x1D'),
        '^' => Some('\x1E'),
        '_' => Some('\x1F'),
        _ => panic!("Unrecognized escape sequence \\^{}", ctl),
    });
    let ascii = (sym('^') * cntrl)
        | seq(&['N', 'U', 'L']).map(|_| Some('\0'))
        | seq(&['S', 'O', 'H']).map(|_| Some('\x01'))
        | seq(&['S', 'T', 'X']).map(|_| Some('\x02'))
        | seq(&['E', 'T', 'X']).map(|_| Some('\x03'))
        | seq(&['E', 'O', 'T']).map(|_| Some('\x04'))
        | seq(&['E', 'N', 'Q']).map(|_| Some('\x05'))
        | seq(&['A', 'C', 'K']).map(|_| Some('\x06'))
        | seq(&['B', 'E', 'L']).map(|_| Some('\x07'))
        | seq(&['B', 'S']).map(|_| Some('\x08'))
        | seq(&['H', 'T']).map(|_| Some('\x09'))
        | seq(&['L', 'F']).map(|_| Some('\x0A'))
        | seq(&['V', 'T']).map(|_| Some('\x0B'))
        | seq(&['F', 'F']).map(|_| Some('\x0C'))
        | seq(&['C', 'R']).map(|_| Some('\x0D'))
        | seq(&['S', 'O']).map(|_| Some('\x0E'))
        | seq(&['S', 'I']).map(|_| Some('\x0F'))
        | seq(&['D', 'L', 'E']).map(|_| Some('\x10'))
        | seq(&['D', 'C', '1']).map(|_| Some('\x11'))
        | seq(&['D', 'C', '2']).map(|_| Some('\x12'))
        | seq(&['D', 'C', '3']).map(|_| Some('\x13'))
        | seq(&['D', 'C', '4']).map(|_| Some('\x14'))
        | seq(&['N', 'A', 'K']).map(|_| Some('\x15'))
        | seq(&['S', 'Y', 'N']).map(|_| Some('\x16'))
        | seq(&['E', 'T', 'B']).map(|_| Some('\x17'))
        | seq(&['C', 'A', 'N']).map(|_| Some('\x18'))
        | seq(&['E', 'M']).map(|_| Some('\x19'))
        | seq(&['S', 'U', 'B']).map(|_| Some('\x1A'))
        | seq(&['E', 'S', 'C']).map(|_| Some('\x1B'))
        | seq(&['F', 'S']).map(|_| Some('\x1C'))
        | seq(&['G', 'S']).map(|_| Some('\x1D'))
        | seq(&['R', 'S']).map(|_| Some('\x1E'))
        | seq(&['U', 'S']).map(|_| Some('\x1F'))
        | seq(&['S', 'P']).map(|_| Some('\x20'))
        | seq(&['D', 'E', 'L']).map(|_| Some('\x7F'));
    let decimal = is_a(|c: char| c.is_digit(10))
        .repeat(1..)
        .convert(|digits| {
            let num_digits = digits.len();
            let dec = digits.into_iter().enumerate().fold(0, |acc, (i, digit)| {
                acc + digit.to_digit(10).expect("invalid digit")
                    * 10u32.pow((num_digits - i - 1) as u32)
            });
            char::try_from(dec).map(Some)
        });
    let octal = (sym('o')
        * is_a(|c: char| c.is_digit(8)).repeat(1..).convert(|octits| {
            let num_octits = octits.len();
            let oct = octits.into_iter().enumerate().fold(0, |acc, (i, octit)| {
                acc + octit.to_digit(8).expect("invalid octit")
                    * 8u32.pow((num_octits - i - 1) as u32)
            });
            char::try_from(oct)
        }))
    .map(Some);
    let hexadecimal = (sym('x')
        * is_a(|c: char| c.is_digit(16))
            .repeat(1..)
            .convert(|hexits| {
                let num_hexits = hexits.len();
                let hex = hexits.into_iter().enumerate().fold(0, |acc, (i, hexit)| {
                    acc + hexit.to_digit(16).expect("invalid hexit")
                        * 16u32.pow((num_hexits - i - 1) as u32)
                });
                char::try_from(hex)
            }))
    .map(Some);
    let escape = sym('\\') * (charesc | ascii | decimal | octal | hexadecimal);
    let r#char = escape | any().map(Some);
    (one_of("\'\"") + many_until(r#char, one_of("\'\""))).convert(|(open, (string, close))| {
        if open == close {
            Ok(String::from_iter(
                string
                    .into_iter()
                    .filter(Option::is_some)
                    // We know it is safe to call Option::unwrap since we only select the Option<char>s
                    // from `string` are that Some, so unwrap cannot panic.
                    .map(Option::unwrap),
            ))
        } else {
            Err(format!(
                "Invalid string literal: string was opened with {} but closed with {}",
                open, close
            ))
        }
    }) - sc()
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

    #[test]
    fn parse_string_literals() {
        let input = &*str_slice_to_vec(r#""\SO\&H"   "#);
        let str_lit = string_lit();
        assert_eq!(str_lit.parse(input), Ok("\x0EH".into()));
    }
}
