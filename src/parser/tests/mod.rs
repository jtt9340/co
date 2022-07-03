use super::*;

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

#[test]
fn parse_exprs() {
    let input = &*str_slice_to_vec(r#"1 + a < 9 - <- chan   "#);
    let expected = Ok(Expr::Binary(
        BinOp::LessThan,
        Box::new(Expr::Binary(
            BinOp::Plus,
            Box::new(Expr::Num(1.0)),
            Box::new(Expr::Variable(Identifier::from("a"))),
        )),
        Box::new(Expr::Binary(
            BinOp::Minus,
            Box::new(Expr::Num(9.0)),
            Box::new(Expr::Unary(
                UnaryOp::Receive,
                Box::new(Expr::Variable(Identifier::from("chan"))),
            )),
        )),
    ));

    assert_eq!(expr().parse(input), expected);

    let input = &*str_slice_to_vec(r#"funFun(null == "ss" + 12, true)    "#);
    let expected = Ok(Expr::Call(
        Identifier::from("funFun"),
        vec![
            Expr::Binary(
                BinOp::Equals,
                Box::new(Expr::Null),
                Box::new(Expr::Binary(
                    BinOp::Plus,
                    Box::new(Expr::Str(String::from("ss"))),
                    Box::new(Expr::Num(12.0)),
                )),
            ),
            Expr::Bool(true),
        ],
    ));

    assert_eq!(expr().parse(input), expected);

    let input = &*str_slice_to_vec(r#"-99 - <- chan + funkyFun(a, false, "hey")   "#);
    let expected = Ok(Expr::Binary(
        BinOp::Plus,
        Box::new(Expr::Binary(
            BinOp::Minus,
            Box::new(Expr::Unary(UnaryOp::Minus, Box::new(Expr::Num(99.0)))),
            Box::new(Expr::Unary(
                UnaryOp::Receive,
                Box::new(Expr::Variable(Identifier::from("chan"))),
            )),
        )),
        Box::new(Expr::Call(
            Identifier::from("funkyFun"),
            vec![
                Expr::Variable(Identifier::from("a")),
                Expr::Bool(false),
                Expr::Str(String::from("hey")),
            ],
        )),
    ));

    assert_eq!(expr().parse(input), expected);
}

#[test]
fn parse_if_stmt() {
    let input = &*str_slice_to_vec(r#"if (name == "Joey") {} "#);
    let expected = Ok(Statement::If {
        condition: Expr::Binary(
            BinOp::Equals,
            Box::new(Expr::Variable(Identifier::from("name"))),
            Box::new(Expr::Str(String::from("Joey"))),
        ),
        body: Vec::new(),
    });

    assert_eq!(stmt().parse(input), expected);
}

#[test]
fn parse_while_loop() {
    let input = &*str_slice_to_vec(r#"while (name == null) {}    "#);
    let expected = Ok(Statement::While {
        condition: Expr::Binary(
            BinOp::Equals,
            Box::new(Expr::Variable(Identifier::from("name"))),
            Box::new(Expr::Null),
        ),
        body: Vec::new(),
    });

    assert_eq!(stmt().parse(input), expected);
}

#[test]
fn parse_var_decl() {
    let input = &*str_slice_to_vec(r#"var name = "Joey";   "#);
    let expected = Ok(Statement::Variable {
        name: Identifier::from("name"),
        init: Expr::Str(String::from("Joey")),
    });

    assert_eq!(stmt().parse(input), expected);
}

#[test]
fn parse_yield_stmt() {
    let input = &*str_slice_to_vec(r#"yield;"#);
    let expected = Ok(Statement::Yield);

    assert_eq!(stmt().parse(input), expected);
}

#[test]
fn parse_spawn_stmt() {
    let input = &*str_slice_to_vec(r#"spawn pi(5000);   "#);
    let expected = Ok(Statement::Spawn(Expr::Call(
        Identifier::from("pi"),
        vec![Expr::Num(5000.0)],
    )));

    assert_eq!(stmt().parse(input), expected);
}

#[test]
fn parse_return_stmt() {
    let input = &*str_slice_to_vec(r#"return;   "#);
    let expected = Ok(Statement::Return(None));

    assert_eq!(stmt().parse(input), expected);

    let input = &*str_slice_to_vec(r#"return 5;      "#);
    let expected = Ok(Statement::Return(Some(Expr::Num(5.0))));

    assert_eq!(stmt().parse(input), expected);
}

#[test]
fn parse_func_def() {
    let input = &*str_slice_to_vec(
        r#"function add(a, b) {
            return a + b;
    }"#,
    );
    let expected = Ok(Statement::FunctionDefinition {
        name: Identifier::from("add"),
        params: vec![Identifier::from("a"), Identifier::from("b")],
        body: vec![Statement::Return(Some(Expr::Binary(
            BinOp::Plus,
            Box::new(Expr::Variable(Identifier::from("a"))),
            Box::new(Expr::Variable(Identifier::from("b"))),
        )))],
    });

    assert_eq!(stmt().parse(input), expected);
}

#[test]
fn parse_assignment() {
    let input = &*str_slice_to_vec(r#"a = 5;     "#);
    let expected = Ok(Statement::Assignment {
        variable: Identifier::from("a"),
        new_value: Expr::Num(5.0),
    });

    assert_eq!(stmt().parse(input), expected);
}

#[test]
fn parse_send_stmt() {
    let input = &*str_slice_to_vec(r#"a + 5 -> chan;    "#);
    let expected = Ok(Statement::Send(
        Expr::Binary(
            BinOp::Plus,
            Box::new(Expr::Variable(Identifier::from("a"))),
            Box::new(Expr::Num(5.0)),
        ),
        Identifier::from("chan"),
    ));

    assert_eq!(stmt().parse(input), expected);
}

#[test]
fn parse_expr_stmt() {
    let input = &*str_slice_to_vec(r#"a;   "#);
    let expected = Ok(Statement::Expr(Expr::Variable(Identifier::from("a"))));

    assert_eq!(stmt().parse(input), expected);
}

#[test]
fn parse_coroutines() {
    let input = &*str_slice_to_vec(include_str!("coroutines.co"));
    let expected = Ok(vec![
        Statement::FunctionDefinition {
            name: Identifier::from("printNums"),
            params: vec![Identifier::from("start"), Identifier::from("end")],
            body: vec![
                Statement::Variable {
                    name: Identifier::from("i"),
                    init: Expr::Variable(Identifier::from("start")),
                },
                Statement::While {
                    condition: Expr::Binary(
                        BinOp::LessThan,
                        Box::new(Expr::Variable(Identifier::from("i"))),
                        Box::new(Expr::Binary(
                            BinOp::Plus,
                            Box::new(Expr::Variable(Identifier::from("end"))),
                            Box::new(Expr::Num(1.0)),
                        )),
                    ),
                    body: vec![
                        Statement::Expr(Expr::Call(
                            Identifier::from("print"),
                            vec![Expr::Variable(Identifier::from("i"))],
                        )),
                        Statement::Yield,
                        Statement::Assignment {
                            variable: Identifier::from("i"),
                            new_value: Expr::Binary(
                                BinOp::Plus,
                                Box::new(Expr::Variable(Identifier::from("i"))),
                                Box::new(Expr::Num(1.0)),
                            ),
                        },
                    ],
                },
            ],
        },
        Statement::Spawn(Expr::Call(
            Identifier::from("printNums"),
            vec![Expr::Num(1.0), Expr::Num(4.0)],
        )),
        Statement::Expr(Expr::Call(
            Identifier::from("printNums"),
            vec![Expr::Num(11.0), Expr::Num(15.0)],
        )),
    ]);

    assert_eq!(program().parse(input), expected);
}

#[test]
fn parse_fib() {
    let input = &*str_slice_to_vec(include_str!("fib.co"));
    let expected = Ok(vec![
        Statement::Variable {
            name: Identifier::from("a"),
            init: Expr::Num(0.0),
        },
        Statement::Variable {
            name: Identifier::from("b"),
            init: Expr::Num(1.0),
        },
        Statement::Variable {
            name: Identifier::from("j"),
            init: Expr::Num(0.0),
        },
        Statement::While {
            condition: Expr::Binary(
                BinOp::LessThan,
                Box::new(Expr::Variable(Identifier::from("j"))),
                Box::new(Expr::Num(6.0)),
            ),
            body: vec![
                Statement::Expr(Expr::Call(
                    Identifier::from("print"),
                    vec![Expr::Variable(Identifier::from("a"))],
                )),
                Statement::Variable {
                    name: Identifier::from("temp"),
                    init: Expr::Variable(Identifier::from("a")),
                },
                Statement::Assignment {
                    variable: Identifier::from("a"),
                    new_value: Expr::Variable(Identifier::from("b")),
                },
                Statement::Assignment {
                    variable: Identifier::from("b"),
                    new_value: Expr::Binary(
                        BinOp::Plus,
                        Box::new(Expr::Variable(Identifier::from("temp"))),
                        Box::new(Expr::Variable(Identifier::from("b"))),
                    ),
                },
                Statement::Assignment {
                    variable: Identifier::from("j"),
                    new_value: Expr::Binary(
                        BinOp::Plus,
                        Box::new(Expr::Variable(Identifier::from("j"))),
                        Box::new(Expr::Num(1.0)),
                    ),
                },
            ],
        },
        Statement::FunctionDefinition {
            name: Identifier::from("fib"),
            params: vec![Identifier::from("n")],
            body: vec![
                Statement::If {
                    condition: Expr::Binary(
                        BinOp::LessThan,
                        Box::new(Expr::Variable(Identifier::from("n"))),
                        Box::new(Expr::Num(2.0)),
                    ),
                    body: vec![Statement::Return(Some(Expr::Variable(Identifier::from(
                        "n",
                    ))))],
                },
                Statement::Return(Some(Expr::Binary(
                    BinOp::Plus,
                    Box::new(Expr::Call(
                        Identifier::from("fib"),
                        vec![Expr::Binary(
                            BinOp::Minus,
                            Box::new(Expr::Variable(Identifier::from("n"))),
                            Box::new(Expr::Num(2.0)),
                        )],
                    )),
                    Box::new(Expr::Call(
                        Identifier::from("fib"),
                        vec![Expr::Binary(
                            BinOp::Minus,
                            Box::new(Expr::Variable(Identifier::from("n"))),
                            Box::new(Expr::Num(1.0)),
                        )],
                    )),
                ))),
            ],
        },
        Statement::Variable {
            name: Identifier::from("i"),
            init: Expr::Num(0.0),
        },
        Statement::While {
            condition: Expr::Binary(
                BinOp::LessThan,
                Box::new(Expr::Variable(Identifier::from("i"))),
                Box::new(Expr::Num(6.0)),
            ),
            body: vec![
                Statement::Expr(Expr::Call(
                    Identifier::from("print"),
                    vec![Expr::Call(
                        Identifier::from("fib"),
                        vec![Expr::Variable(Identifier::from("i"))],
                    )],
                )),
                Statement::Assignment {
                    variable: Identifier::from("i"),
                    new_value: Expr::Binary(
                        BinOp::Plus,
                        Box::new(Expr::Variable(Identifier::from("i"))),
                        Box::new(Expr::Num(1.0)),
                    ),
                },
            ],
        },
    ]);

    assert_eq!(program().parse(input), expected);
}

#[test]
fn parse_ping() {
    let input = &*str_slice_to_vec(include_str!("ping.co"));
    let expected = Ok(vec![
        Statement::Variable {
            name: Identifier::from("chan"),
            init: Expr::Call(Identifier::from("newChannel"), vec![]),
        },
        Statement::FunctionDefinition {
            name: Identifier::from("player"),
            params: vec![Identifier::from("name")],
            body: vec![Statement::While {
                condition: Expr::Bool(true),
                body: vec![
                    Statement::Variable {
                        name: Identifier::from("n"),
                        init: Expr::Unary(
                            UnaryOp::Receive,
                            Box::new(Expr::Variable(Identifier::from("chan"))),
                        ),
                    },
                    Statement::If {
                        condition: Expr::Binary(
                            BinOp::Equals,
                            Box::new(Expr::Variable(Identifier::from("n"))),
                            Box::new(Expr::Str(String::from("done"))),
                        ),
                        body: vec![
                            Statement::Expr(Expr::Call(
                                Identifier::from("print"),
                                vec![Expr::Binary(
                                    BinOp::Plus,
                                    Box::new(Expr::Variable(Identifier::from("name"))),
                                    Box::new(Expr::Str(String::from(" done"))),
                                )],
                            )),
                            Statement::Return(None),
                        ],
                    },
                    Statement::Expr(Expr::Call(
                        Identifier::from("print"),
                        vec![Expr::Binary(
                            BinOp::Plus,
                            Box::new(Expr::Binary(
                                BinOp::Plus,
                                Box::new(Expr::Variable(Identifier::from("name"))),
                                Box::new(Expr::Str(String::from(" "))),
                            )),
                            Box::new(Expr::Variable(Identifier::from("n"))),
                        )],
                    )),
                    Statement::If {
                        condition: Expr::Binary(
                            BinOp::GreaterThan,
                            Box::new(Expr::Variable(Identifier::from("n"))),
                            Box::new(Expr::Num(0.0)),
                        ),
                        body: vec![Statement::Send(
                            Expr::Binary(
                                BinOp::Minus,
                                Box::new(Expr::Variable(Identifier::from("n"))),
                                Box::new(Expr::Num(1.0)),
                            ),
                            Identifier::from("chan"),
                        )],
                    },
                    Statement::If {
                        condition: Expr::Binary(
                            BinOp::Equals,
                            Box::new(Expr::Variable(Identifier::from("n"))),
                            Box::new(Expr::Num(0.0)),
                        ),
                        body: vec![
                            Statement::Expr(Expr::Call(
                                Identifier::from("print"),
                                vec![Expr::Binary(
                                    BinOp::Plus,
                                    Box::new(Expr::Variable(Identifier::from("name"))),
                                    Box::new(Expr::Str(String::from(" done"))),
                                )],
                            )),
                            Statement::Send(
                                Expr::Str(String::from("done")),
                                Identifier::from("chan"),
                            ),
                            Statement::Return(None),
                        ],
                    },
                ],
            }],
        },
        Statement::Spawn(Expr::Call(
            Identifier::from("player"),
            vec![Expr::Str(String::from("ping"))],
        )),
        Statement::Spawn(Expr::Call(
            Identifier::from("player"),
            vec![Expr::Str(String::from("pong"))],
        )),
        Statement::Send(Expr::Num(10.0), Identifier::from("chan")),
    ]);

    assert_eq!(program().parse(input), expected);
}
