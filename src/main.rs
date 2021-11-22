mod ast;
mod parser;

fn main() {
    let test = "/* This is a comment";
    let test_input = test.chars().collect::<Vec<_>>();
    let parser = parser::sc();
    println!("{:?}", parser.parse(&test_input));
}
