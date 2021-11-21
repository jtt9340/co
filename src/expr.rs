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

#[derive(Eq, PartialEq, Debug)]
pub enum Expr {
    /// The literal `null`. Evaluates to the null value.
    Null,
    /// The boolean literals `true` and `false`.
    Bool(bool),
    /// String literals.
    Str(String),
    /// An integer literal.
    Num(i64),
    /// A bare word starting with an alphabetic character.
    /// Refers to the value of a variable at runtime.
    Variable(Identifier),
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
            Str(s) => write!(f, "{}", s),
            Num(n) => write!(f, "{}", n),
            Variable(ident) => write!(f, "{}", ident),
            Binary(op, lhs, rhs) => write!(f, "{} {} {}", lhs, op, rhs),
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

#[derive(Eq, PartialEq, Debug)]
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
    use std::collections::HashMap;
    use super::*;

    #[test]
    fn fmt_bin_op() {
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
}
