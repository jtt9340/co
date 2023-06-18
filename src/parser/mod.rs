use std::collections::HashMap;
use std::iter::once;

use once_cell::sync::Lazy;
use pom::parser::{Parser as PomParser, *};

use utils::*;

use super::ast::{BinOp, Expr, Identifier, Program, Statement, UnaryOp};

#[cfg(test)]
mod tests;
mod utils;

/// Type alias for a [`pom::parser::Parser`] that parses streams of [`char`]aracters and outputs
/// [`String`]s.
///
/// The lifetime parameter `'a` is the lifetime of the data source being parsed.
pub type Parser<'a> = pom::parser::Parser<'a, char, String>;

/// Type describing a binary operator's precedence.
type PrecedenceScore = i16;

static BINOP_PRECEDENCE: Lazy<HashMap<&str, PrecedenceScore>> = Lazy::new(|| {
    HashMap::from([
        ("==", 10),
        ("!=", 10),
        ("<", 20),
        (">", 20),
        ("<=", 20),
        (">=", 20),
        ("+", 30),
        ("-", 30),
        ("*", 40),
        ("/", 40),
    ])
});

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

/// Get a parser that recognizes the semicolon lexeme, i.e. `;`.
pub fn semi<'a>() -> PomParser<'a, char, ()> {
    lexeme(sym(';')).discard()
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
    lexeme(one_of("\'\"") + many_until(r#char, one_of("\'\""))).convert(
        |(open, (string, close))| {
            if open == close {
                Ok(String::from_iter(string.into_iter().flatten()))
            } else {
                Err(format!(
                    "Invalid string literal: string was opened with {} but closed with {}",
                    open, close
                ))
            }
        },
    )
}

/// Get a parser that parses number literals.
pub fn number<'a>() -> PomParser<'a, char, f64> {
    lexeme(PomParser::new(
        move |input: &'a [char], start: usize| match fast_float::parse_partial::<f64, _>(
            String::from_iter(input.iter().skip(start)),
        ) {
            Ok((num, num_digits)) => Ok((num, start + num_digits)),
            Err(e) => Err(pom::Error::Custom {
                message: e.to_string(),
                position: start,
                inner: None,
            }),
        },
    ))
}

fn primary<'a>() -> PomParser<'a, char, Expr> {
    PomParser::new(move |input: &'a [char], start: usize| {
        // First attempt to parse null literals
        if let Ok((_null, new_pos)) = symbol(&['n', 'u', 'l', 'l']).parse_at(input, start) {
            return Ok((Expr::Null, new_pos));
        }

        // Then "true"
        if let Ok((_true, new_pos)) = symbol(&['t', 'r', 'u', 'e']).parse_at(input, start) {
            return Ok((Expr::Bool(true), new_pos));
        }

        // Then "false"
        if let Ok((_false, new_pos)) = symbol(&['f', 'a', 'l', 's', 'e']).parse_at(input, start) {
            return Ok((Expr::Bool(false), new_pos));
        }

        // Then a string literal
        if let Ok((string, new_pos)) = string_lit().parse_at(input, start) {
            return Ok((Expr::Str(string), new_pos));
        }

        // Then a numeric literal
        if let Ok((num, new_pos)) = number().parse_at(input, start) {
            return Ok((Expr::Num(num), new_pos));
        }

        // Then a function definition
        let func_def = symbol(&['f', 'u', 'n', 'c', 't', 'i', 'o', 'n'])
            * parens(list(identifier(), lexeme(sym(','))))
            + braces(stmt().repeat(0..));
        if let Ok(((params, body), new_pos)) = func_def.parse_at(input, start) {
            return Ok((Expr::Lambda { params, body }, new_pos));
        }

        // Then an identifier
        if let Ok((ident, new_pos)) = identifier().parse_at(input, start) {
            return Ok((Expr::Variable(ident), new_pos));
        }

        // Finally, a parenthesized expression
        if let Ok((expr, new_pos)) = parens(expr()).parse_at(input, start) {
            return Ok((expr, new_pos));
        }

        // None of the above
        Err(pom::Error::Custom {
            message: "Unrecognized term".into(),
            position: start,
            inner: None,
        })
    })
}

/// Get a parser that parses terms in an expression.
fn term<'a>() -> PomParser<'a, char, Expr> {
    (primary() + (parens(list(expr(), lexeme(sym(','))))).repeat(0..))
        .map(|(callee, args_lists)| args_lists_to_expr(callee, args_lists))
}

fn is_operator_char(c: char) -> bool {
    !c.is_ascii_alphanumeric() && !" \"(,".contains(c)
}

/// Parse terms that are preceded by zero or more unary operators.
pub fn unary<'a>() -> PomParser<'a, char, Expr> {
    PomParser::new(move |input: &'a [char], start: usize| {
        if let Some(&cur_tok) = input.get(start) {
            let term_idx = input
                .iter()
                .skip(start)
                .enumerate()
                .find(|(_, &chr)| !is_operator_char(chr))
                .map(|(idx, _)| idx + start)
                .unwrap_or_else(|| input.len() - 1);

            if !is_operator_char(cur_tok) {
                return term().parse_at(input, start);
            }

            let mut index = 0;
            loop {
                let pos = start + index;
                if pos == term_idx + 1 {
                    return Err(pom::Error::Mismatch {
                        message: format!(
                            "Unrecognized unary operator: {:?}",
                            &input[start..(pos - 1)],
                        ),
                        position: pos,
                    });
                }

                if let Ok(unary_op) =
                    String::from_iter(input.iter().skip(start).take(index)).parse::<UnaryOp>()
                {
                    let non_whitespace_idx = input
                        .iter()
                        .skip(pos)
                        .enumerate()
                        .find(|(_, &chr)| !chr.is_ascii_whitespace())
                        .map(|(idx, _)| pos + idx)
                        .unwrap_or_else(|| input.len());

                    return match call(unary).parse_at(input, non_whitespace_idx) {
                        Ok((operand, new_pos)) => {
                            Ok((Expr::Unary(unary_op, Box::new(operand)), new_pos))
                        }
                        Err(e) => Err(pom::Error::Custom {
                            message: format!("Invalid operand following {}", unary_op),
                            position: non_whitespace_idx,
                            inner: Some(Box::new(e)),
                        }),
                    };
                }

                index += 1;
            }
        }

        Err(pom::Error::Incomplete)
    })
}

fn binop_rhs<'a>(expr_prec: PrecedenceScore, expr: Expr) -> PomParser<'a, char, Expr> {
    let binop = || {
        symbol(&['*'])
            | symbol(&['/'])
            | symbol(&['+'])
            | (symbol(&['-']) - !symbol(&['>']))
            | symbol(&['<', '='])
            | symbol(&['>', '='])
            | symbol(&['<'])
            | symbol(&['>'])
            | symbol(&['=', '='])
            | symbol(&['!', '='])
    };

    PomParser::new(move |input: &'a [char], mut start: usize| {
        let mut lhs = expr.clone();

        // Since a binary expression can contain multiple
        // sub-expressions, we loop until we parse them all.
        loop {
            let (bin_op, new_pos) = match binop().parse_at(input, start) {
                Ok((bin_op, new_pos)) => (bin_op, new_pos),
                Err(_) => return Ok((lhs, start)),
            };
            let tok_prec = BINOP_PRECEDENCE[bin_op.as_str()];

            if tok_prec < expr_prec {
                return Ok((lhs, start));
            }

            let (mut rhs, new_pos) = unary().parse_at(input, new_pos)?;

            start = new_pos;

            let next_prec = binop()
                .parse_at(input, new_pos)
                .map_or(-1, |(cur_tok, _)| BINOP_PRECEDENCE[cur_tok.as_str()]);

            if tok_prec < next_prec {
                let rhs_pos_pair = binop_rhs(tok_prec + 1, rhs).parse_at(input, new_pos)?;
                rhs = rhs_pos_pair.0;
                start = rhs_pos_pair.1;
            }

            lhs = Expr::Binary(
                bin_op.parse::<BinOp>().unwrap(),
                Box::new(lhs),
                Box::new(rhs),
            );
        }
    })
}

/// Expression parser. An expression is one or more unary terms separated by binary operators.
///
/// The parsers respects precedences as declared in `BINOP_PRECEDENCE`.
pub fn expr<'a>() -> PomParser<'a, char, Expr> {
    PomParser::new(move |input: &'a [char], start: usize| {
        let (lhs, new_pos) = unary().parse_at(input, start)?;
        binop_rhs(0, lhs).parse_at(input, new_pos)
    })
}

fn control_structure(keyword: &[char]) -> PomParser<char, (Expr, Vec<Statement>)> {
    let cond_parser = parens(expr());
    let body_parser = braces(call(stmt).repeat(0..));
    symbol(keyword) * cond_parser + body_parser
}

/// Statement parser.
pub fn stmt<'a>() -> PomParser<'a, char, Statement> {
    let r#if =
        control_structure(&['i', 'f']).map(|(condition, body)| Statement::If { condition, body });
    let r#while = control_structure(&['w', 'h', 'i', 'l', 'e'])
        .map(|(condition, body)| Statement::While { condition, body });
    let var = ((symbol(&['v', 'a', 'r']) * identifier()) + (lexeme(sym('=')) * expr() - semi()))
        .map(|(var, val)| Statement::Variable {
            name: var,
            init: val,
        });
    let r#yield = (symbol(&['y', 'i', 'e', 'l', 'd']) - semi()).map(|_| Statement::Yield);
    let spawn = (symbol(&['s', 'p', 'a', 'w', 'n']) * expr() - semi()).map(Statement::Spawn);
    let r#return =
        (symbol(&['r', 'e', 't', 'u', 'r', 'n']) * expr().opt() - semi()).map(Statement::Return);
    let function = {
        let prototype_parser = symbol(&['f', 'u', 'n', 'c', 't', 'i', 'o', 'n']) * identifier();
        let args_parser = parens(list(identifier(), lexeme(sym(','))));
        let body_parser = braces(call(stmt).repeat(0..));
        (prototype_parser + args_parser + body_parser)
            .map(|((name, params), body)| Statement::FunctionDefinition { name, params, body })
    };
    let assign = (identifier() + (lexeme(sym('=')) * expr() - semi())).map(|(var, val)| {
        Statement::Assignment {
            variable: var,
            new_value: val,
        }
    });
    let send = (expr() + (symbol(&['-', '>']) * identifier() - semi()))
        .map(|(value, recipient)| Statement::Send(value, recipient));
    let expr_stmt = (expr() - semi()).map(Statement::Expr);
    r#if | r#while | var | r#yield | spawn | r#return | function | assign | send | expr_stmt
}

pub fn program<'a>() -> PomParser<'a, char, Program> {
    sc() * stmt().repeat(0..) - end()
}
