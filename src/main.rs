mod ast;
mod parser;

use std::io::{stdin, BufRead};

fn main() {
    let stdin = stdin();
    let handle = stdin.lock();

    print!("> ");
    for buf in handle.lines().map(Result::unwrap) {
        let last_parser_char = buf.find(char::is_whitespace).unwrap_or(buf.len());
        let parser = &buf[..last_parser_char];
        let first_input_char = match (&buf[last_parser_char..]).find(|c: char| !c.is_whitespace()) {
            Some(index) => last_parser_char + index,
            None => buf.len(),
        };
        let input = &buf[first_input_char..];
        let input = input.chars().collect::<Vec<_>>();
        match parser {
            "spaceConsumer" => println!("{:?}", parser::sc().parse(&input)),
            "identifier" => println!("{:?}", parser::identifier().parse(&input)),
            "stringLiteral" => println!("{:?}", parser::string_lit().parse(&input)),
            "number" => println!("{:?}", parser::number().parse(&input)),
            p => {
                eprintln!("Unrecognized parser \"{}\". Options are: spaceConsumer, identifier, stringLiteral, or number", p);
                continue;
            }
        }
        print!("> ");
    }
}
