use std::fmt::Write;

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

#[derive(PartialEq, Debug)]
pub enum Expr {
    /// The literal `null`. Evaluates to the null value.
    Null,
    /// The boolean literals `true` and `false`.
    Bool(bool),
    /// String literals.
    Str(String),
    /// An integer literal.
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
                let bin_op_s = format!("({} {} {})", lhs, op, rhs);
                // let bin_op_s = bin_op_s.trim_matches(|c| c == '(' || c == ')');
                f.write_str(&bin_op_s)
            }
            Call(fname, args) => write!(
                f,
                "{}({})",
                fname,
                args.into_iter()
                    .map(|arg| format!("{}", arg))
                    .collect::<Vec<_>>()
                    .join(", ".into())
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
    If { condition: Expr, body: Vec<Expr> },
    /// While loop. Evaluates `condition` and runs the given `Vec` of statements if the `condition`
    /// is true. Repeats execution until the `condition` is false.
    While { condition: Expr, body: Vec<Expr> },
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
}

#[cfg(test)]
mod tests {
    use super::*;
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
    fn fmt_bin_expr() {
        let bin_expr = Expr::Binary(
            BinOp::Plus,
            Box::new(Expr::Num(2.0)),
            Box::new(Expr::Num(3.0)),
        );
        assert_eq!(&bin_expr.to_string(), "(2 + 3)");

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
        assert_eq!(&bin_expr.to_string(), "((b * b) - (4 * (a * c)))");
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
}
