use std::fmt::{Formatter, Write};

pub type Identifier = String;

#[derive(Eq, PartialEq, Debug, Hash)]
pub enum BinOp {
    Plus,
    Minus,
    Times,
    Divide,
    Equals,
    NotEquals,
    LessThan,
    LessThanEqual,
    GreaterThan,
    GreaterThanEqual,
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use BinOp::*;

        match self {
            Plus => f.write_char('+'),
            Minus => f.write_char('-'),
            Times => f.write_char('*'),
            Divide => f.write_char('/'),
            Equals => f.write_str("=="),
            NotEquals => f.write_str("!="),
            LessThan => f.write_char('<'),
            LessThanEqual => f.write_str("<="),
            GreaterThan => f.write_char('>'),
            GreaterThanEqual => f.write_str(">="),
        }
    }
}

impl std::str::FromStr for BinOp {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut chars = s.chars();
        let fst = match chars.next() {
            Some(chr) => chr,
            None => return Err("No characters to parse into a binary operator"),
        };

        match fst {
            '+' => {
                if chars.all(char::is_whitespace) {
                    Ok(BinOp::Plus)
                } else {
                    Err("Extraneous characters in binary operator besides +")
                }
            },
            '-' => {
                // TODO: Do we need to handle -> ?
                if chars.all(char::is_whitespace) {
                    Ok(BinOp::Minus)
                } else {
                    Err("Extraneous characters in binary operator besides -")
                }
            }
            '*' => {
                if chars.all(char::is_whitespace) {
                    Ok(BinOp::Times)
                } else {
                    Err("Extraneous characters in binary operator besides *")
                }
            }
            '/' => {
                if chars.all(char::is_whitespace) {
                    Ok(BinOp::Divide)
                } else {
                    Err("Extraneous characters in binary operator besides /")
                }
            }
            '=' => {
                if let Some('=') = chars.next() {
                    if chars.all(char::is_whitespace) {
                        Ok(BinOp::Equals)
                    } else {
                        Err("Extraneous characters in binary operator besides ==")
                    }
                } else {
                    Err("Unrecognized binary operator")
                }
            }
            '!' => {
                if let Some('=') = chars.next() {
                    if chars.all(char::is_whitespace) {
                        Ok(BinOp::NotEquals)
                    } else {
                        Err("Extraneous characters in binary operator besides !=")
                    }
                } else {
                    Err("Unrecognized binary operator")
                }
            }
            '<' => {
                if let Some(snd) = chars.next() {
                    if snd == '=' && chars.all(char::is_whitespace) {
                        Ok(BinOp::LessThanEqual)
                    } else if snd == '=' {
                        Err("Extraneous characters in binary operator besides <=")
                    } else if snd.is_whitespace() && chars.all(char::is_whitespace) {
                        Ok(BinOp::LessThan)
                    } else {
                        Err("Extraneous characters in binary operator besides <")
                    }
                } else {
                    Ok(BinOp::LessThan)
                }
            }
            '>' => {
                if let Some(snd) = chars.next() {
                    if snd == '=' && chars.all(char::is_whitespace) {
                        Ok(BinOp::GreaterThanEqual)
                    } else if snd == '=' {
                        Err("Extraneous characters in binary operator besides >=")
                    } else if snd.is_whitespace() && chars.all(char::is_whitespace) {
                       Ok(BinOp::GreaterThan) 
                    } else {
                        Err("Extraneous characters in binary operator besides >")
                    }
                } else {
                    Ok(BinOp::GreaterThan)
                }
            }
            _ => Err("Unrecognized binary operator"),
        }
    }
}

#[derive(PartialEq, Debug)]
pub enum Expr {
    /// The literal `null`. Evaluates to the null value.
    Null,
    /// The boolean literals `true` and `false`.
    Bool(bool),
    /// String literals.
    Str(String),
    /// An number literal.
    Num(f64),
    /// A bare word starting with an alphabetic character.
    /// Refers to the value of a variable at runtime.
    Variable(Identifier),
    /// The unary negation of an identifier, such as `-b`.
    UnaryMinus(Identifier),
    /// A binary operation on two expressions.
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// A function call.
    Call(Identifier, Vec<Expr>),
    /// Expression for receiving a value from a channel.
    Receive(Box<Expr>),
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Expr::*;

        match self {
            Null => f.write_str("null"),
            Bool(b) => write!(f, "{}", b),
            Str(s) => write!(f, "\"{}\"", s),
            Num(n) => write!(f, "{}", n),
            Variable(ident) => write!(f, "{}", ident),
            UnaryMinus(ident) => write!(f, "-{}", ident),
            Binary(op, lhs, rhs) => {
                let lhs_s = if let Binary(_, _, _) = lhs.as_ref() {
                    format!("({})", lhs)
                } else {
                    format!("{}", lhs)
                };

                let rhs_s = if let Binary(_, _, _) = rhs.as_ref() {
                    format!("({})", rhs)
                } else {
                    format!("{}", rhs)
                };

                write!(f, "{} {} {}", lhs_s, op, rhs_s)
            }
            Call(fname, args) => write!(
                f,
                "{}({})",
                fname,
                args.iter()
                    .map(|arg| format!("{}", arg))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Receive(expr) => write!(f, "<- {}", expr),
        }
    }
}

#[derive(PartialEq, Debug)]
pub enum Statement {
    /// A statement containing a single expression, such as `1 + 2;`.
    Expr(Expr),
    /// A statement that declares a variable and assigns a value to that variable, such as
    /// `var a = 5;`.
    Variable { name: Identifier, init: Expr },
    /// A statement that assigns a new value to a pre-declared variable, such as
    /// `a = 10;`.
    Assignment {
        variable: Identifier,
        new_value: Expr,
    },
    /// If statement. Evaluates `condition` and runs the given `Vec` of statements if the `condition`
    /// is true.
    If {
        condition: Expr,
        body: Vec<Statement>,
    },
    /// While loop. Evaluates `condition` and runs the given `Vec` of statements if the `condition`
    /// is true. Repeats execution until the `condition` is false.
    While {
        condition: Expr,
        body: Vec<Statement>,
    },
    /// Function definition, including the name of the function, a list of zero or more parameters,
    /// and body containing zero or more statements.
    FunctionDefinition {
        name: Identifier,
        params: Vec<Identifier>,
        body: Vec<Statement>,
    },
    /// A return statement. Some functions don't return a value, in which case the given expression
    /// is `None` and the return statement looks like `return;`. Otherwise, the function returns
    /// exactly one value, the given expression is `Some(returned_value)`, and the return statement
    /// looks like `return value;`.
    Return(Option<Expr>),
    /// Yield statement for suspending the current thread of computation.
    Yield,
    /// Spawn statement for executing the evaluation of an expression in another thread of
    /// computation.
    Spawn(Expr),
    /// Statement that sends an expression's value to a channel represented by an identifier.
    Send(Expr, Identifier),
}

fn stringify_control_structure<'a>(
    name: &str,
    cond: &Expr,
    body: impl IntoIterator<Item = &'a Statement>,
) -> String {
    let mut stmt = format!("{} ({}) {{\n", name, cond);
    for line in body.into_iter() {
        let stmt_s = line.to_string();
        for l in stmt_s.lines() {
            stmt.push('\t');
            stmt.push_str(l);
            stmt.push('\n');
        }
    }
    stmt + "}"
}

impl std::fmt::Display for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Statement::*;

        match self {
            Expr(e) => write!(f, "{};", e),
            Variable { name, init } => write!(f, "var {} = {};", name, init),
            Assignment {
                variable: var,
                new_value,
            } => write!(f, "{} = {};", var, new_value),
            If {
                condition: cond,
                body,
            } => write!(f, "{}", stringify_control_structure("if", cond, body)),
            While {
                condition: cond,
                body,
            } => write!(f, "{}", stringify_control_structure("while", cond, body)),
            FunctionDefinition {
                name,
                params: args,
                body,
            } => {
                let mut func_def = format!("function {}(", name);
                for (idx, arg) in args.iter().enumerate() {
                    func_def.push_str(arg);
                    if idx < args.len() - 1 {
                        func_def.push_str(", ");
                    }
                }
                func_def.push_str(") {\n");
                for line in body.iter() {
                    let stmt_s = line.to_string();
                    for l in stmt_s.lines() {
                        func_def.push('\t');
                        func_def.push_str(l);
                        func_def.push('\n');
                    }
                }
                write!(f, "{}}}", func_def)
            }
            Return(Some(val)) => write!(f, "return {};", val),
            Return(None) => f.write_str("return;"),
            Yield => f.write_str("yield;"),
            Spawn(e) => write!(f, "spawn {};", e),
            Send(expr, chan) => write!(f, "{} -> {};", expr, chan),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::array::IntoIter;
    use std::collections::HashMap;

    #[test]
    fn fmt_bin_op() {
        // I could have written each of these are their own unit test but I decided to combine them.
        let expected = HashMap::from([
            (BinOp::Plus, "+"),
            (BinOp::Minus, "-"),
            (BinOp::Times, "*"),
            (BinOp::Divide, "/"),
            (BinOp::Equals, "=="),
            (BinOp::NotEquals, "!="),
            (BinOp::LessThan, "<"),
            (BinOp::LessThanEqual, "<="),
            (BinOp::GreaterThan, ">"),
            (BinOp::GreaterThanEqual, ">="),
        ]);

        for (bin_op, expected) in expected {
            assert_eq!(&bin_op.to_string(), expected);
        }
    }

    #[test]
    fn parse_bin_op() {
        let expected = HashMap::from([
            (BinOp::Plus, "+    "),
            (BinOp::Minus, "-   "),
            (BinOp::Times, "*     "),
            (BinOp::Divide, "/      "),
            (BinOp::Equals, "==   "),
            (BinOp::NotEquals, "!=   "),
            (BinOp::LessThan, "<    "),
            (BinOp::LessThanEqual, "<=    "),
            (BinOp::GreaterThan, ">     "),
            (BinOp::GreaterThanEqual, ">=   "),
        ]);

        for (bin_op, s) in expected {
            assert_eq!(Ok(bin_op), s.parse());
        }

        for bad_case in IntoIter::new(["+    ~", "->", "** ", " &", "!?", "=!  ", "<   = "]) {
            assert!(bad_case.parse::<BinOp>().is_err());
        }
    }

    #[test]
    fn fmt_null_expr() {
        let expr = Expr::Null;
        assert_eq!(&expr.to_string(), "null");
    }

    #[test]
    fn fmt_bool_expr() {
        let true_lit = Expr::Bool(true);
        assert_eq!(&true_lit.to_string(), "true");

        let false_lit = Expr::Bool(false);
        assert_eq!(&false_lit.to_string(), "false");
    }

    #[test]
    fn fmt_str_expr() {
        let str_lit = Expr::Str(String::from("hello"));
        assert_eq!(&str_lit.to_string(), "\"hello\"");

        let str_lit = Expr::Str(String::default());
        assert_eq!(&str_lit.to_string(), "\"\"");
    }

    #[test]
    fn fmt_num_expr() {
        let num_lit = Expr::Num(3.14);
        assert_eq!(&num_lit.to_string(), "3.14");

        let num_lit = Expr::Num(0.0);
        assert_eq!(&num_lit.to_string(), "0");

        let num_lit = Expr::Num(-169.0);
        assert_eq!(&num_lit.to_string(), "-169");
    }

    #[test]
    fn fmt_var_expr() {
        let ident = Expr::Variable(Identifier::from("i"));
        assert_eq!(&ident.to_string(), "i");
    }

    #[test]
    fn fmt_unm_expr() {
        let unary_minus = Expr::UnaryMinus(Identifier::from("b"));
        assert_eq!(&unary_minus.to_string(), "-b");
    }

    #[test]
    fn fmt_bin_expr() {
        let bin_expr = Expr::Binary(
            BinOp::Plus,
            Box::new(Expr::Num(2.0)),
            Box::new(Expr::Num(3.0)),
        );
        assert_eq!(&bin_expr.to_string(), "2 + 3");

        let bin_expr = Expr::Binary(
            BinOp::Minus,
            Box::new(Expr::Binary(
                BinOp::Times,
                Box::new(Expr::Variable(Identifier::from("b"))),
                Box::new(Expr::Variable(Identifier::from("b"))),
            )),
            Box::new(Expr::Binary(
                BinOp::Times,
                Box::new(Expr::Num(4.0)),
                Box::new(Expr::Binary(
                    BinOp::Times,
                    Box::new(Expr::Variable(Identifier::from("a"))),
                    Box::new(Expr::Variable(Identifier::from("c"))),
                )),
            )),
        );
        assert_eq!(&bin_expr.to_string(), "(b * b) - (4 * (a * c))");
    }

    #[test]
    fn fmt_call_expr() {
        let call = Expr::Call(
            Identifier::from("foo"),
            vec![
                Expr::Str(String::from("a")),
                Expr::Variable(Identifier::from("b")),
                Expr::Num(1.0),
            ],
        );
        assert_eq!(&call.to_string(), "foo(\"a\", b, 1)");
    }

    #[test]
    fn fmt_recv_expr() {
        let recv = Expr::Receive(Box::new(Expr::Variable(Identifier::from("chan"))));
        assert_eq!(&recv.to_string(), "<- chan");
    }

    #[test]
    fn fmt_expr_stmt() {
        let stmt = Statement::Expr(Expr::Binary(
            BinOp::Plus,
            Box::new(Expr::Num(1.0)),
            Box::new(Expr::Num(2.0)),
        ));
        assert_eq!(&stmt.to_string(), "1 + 2;");
    }

    #[test]
    fn fmt_var_decl() {
        let decl = Statement::Variable {
            name: Identifier::from("a"),
            init: Expr::Num(1.0),
        };
        assert_eq!(&decl.to_string(), "var a = 1;");
    }

    #[test]
    fn fmt_assignment_stmt() {
        let stmt = Statement::Assignment {
            variable: Identifier::from("a"),
            new_value: Expr::Num(5.0),
        };
        assert_eq!(&stmt.to_string(), "a = 5;");
    }

    #[test]
    fn fmt_if_stmt() {
        let if_stmt = Statement::If {
            condition: Expr::Bool(true),
            body: vec![Statement::Expr(Expr::Num(4.0))],
        };
        assert_eq!(
            &if_stmt.to_string(),
            "if (true) {\n\
        \t4;\n\
        }"
        );

        let nested_if_stmt = Statement::If {
            condition: Expr::Bool(true),
            body: vec![if_stmt],
        };
        assert_eq!(
            &nested_if_stmt.to_string(),
            "if (true) {\n\
        \tif (true) {\n\
        \t\t4;\n\
        \t}\n\
        }"
        );
    }

    #[test]
    fn fmt_while_loop() {
        let while_loop = Statement::While {
            condition: Expr::Bool(true),
            body: vec![Statement::While {
                condition: Expr::Bool(true),
                body: vec![Statement::Expr(Expr::Num(34.0))],
            }],
        };
        assert_eq!(
            &while_loop.to_string(),
            "while (true) {\n\
        \twhile (true) {\n\
        \t\t34;\n\
        \t}\n\
        }"
        )
    }

    #[test]
    fn fmt_func_def() {
        let func_def = Statement::FunctionDefinition {
            name: Identifier::from("foo"),
            params: vec![Identifier::from("a"), Identifier::from("b")],
            body: vec![Statement::Return(Some(Expr::Binary(
                BinOp::Plus,
                Box::new(Expr::Variable(Identifier::from("a"))),
                Box::new(Expr::Variable(Identifier::from("b"))),
            )))],
        };
        assert_eq!(
            &func_def.to_string(),
            "function foo(a, b) {\n\
        \treturn a + b;\n\
        }"
        );
    }

    #[test]
    fn fmt_return() {
        let void_return = Statement::Return(None);
        assert_eq!(&void_return.to_string(), "return;");

        let value_return = Statement::Return(Some(Expr::Variable(Identifier::from('e'))));
        assert_eq!(&value_return.to_string(), "return e;");
    }

    #[test]
    fn fmt_yield() {
        let yield_stmt = Statement::Yield;
        assert_eq!(&yield_stmt.to_string(), "yield;");
    }

    #[test]
    fn fmt_spawn() {
        let spawn = Statement::Spawn(Expr::Call(
            Identifier::from("producer"),
            vec![Expr::Num(3.0)],
        ));
        assert_eq!(&spawn.to_string(), "spawn producer(3);");
    }

    #[test]
    fn fmt_send() {
        let send = Statement::Send(
            Expr::Binary(
                BinOp::Plus,
                Box::new(Expr::Num(1.0)),
                Box::new(Expr::Call(Identifier::from("square"), vec![Expr::Num(3.0)])),
            ),
            Identifier::from("someChannel"),
        );
        assert_eq!(&send.to_string(), "1 + square(3) -> someChannel;");
    }
}
