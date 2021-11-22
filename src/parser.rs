use pom::parser::*;

/// Get a parser that parses the start of a single-line comment: `//`.
fn line_start<'a>() -> Parser<'a, char, char> {
    sym('/') * sym('/')
}

/// Get a parser that parses the start of a block comment: `/*`.
fn block_start<'a>() -> Parser<'a, char, char> {
    sym('/') * sym('*')
}

/// Get a parser that parses the end of a block comment: `*/`.
fn block_end<'a>() -> Parser<'a, char, char> {
    sym('*') * sym('/')
}

/// Get a parser than can parse nested block comments.
fn block<'a>() -> Parser<'a, char, char> {
    block_start() * any().repeat(0..) * call(block).opt() * any().repeat(0..) * block_end()
}

/// The space consumer parser. This parser dictates what's ignored while parsing source code.
/// "Space" is anything considered whitespace by [`char::is_whitespace`]. This parser also ignores
/// single line comments (anything starting with `//` and ending at the end of a line) and block
/// comments (anything in between `/*` and `*/`). Block comments can be nested.
pub fn sc<'a>() -> Parser<'a, char, ()> {
    let sp = is_a(char::is_whitespace);
    let line = line_start() * any().repeat(0..) * sym('\n');
    let block = block();
    (sp | line | block).repeat(0..).discard()
}
