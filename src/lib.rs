#![deny(unsafe_code)]
#![warn(
    clippy::all,
    explicit_outlives_requirements,
    let_underscore_drop,
    missing_copy_implementations,
    missing_debug_implementations,
    noop_method_call,
    rust_2021_incompatible_closure_captures,
    unreachable_pub,
    unused_results,
    variant_size_differences
)]
#![allow(clippy::new_without_default)]
// There are plenty of warnings about dead_code in the beginning
#![allow(dead_code)]
// TEMPORARY
#![allow(unused_variables)]

mod context;
mod expression;
mod intern;
mod state;
mod ty;
mod variable;

mod error;

fn synthesize_with_state(
    expression: expression::Expression,
    state: &mut state::State,
) -> ::std::result::Result<ty::Type, crate::error::Error>
{
    let mut context = context::Context::initial();
    let (ty, new_context) = expression.synthesize(state, &mut context)?;

    Ok(ty.apply_context(state, new_context))
}

fn synthesize(
    expression: expression::Expression,
) -> ::std::result::Result<ty::Type, crate::error::Error>
{
    let mut state = state::State::initial();

    synthesize_with_state(expression, &mut state)
}

#[cfg(test)]
mod tests
{
    use crate::{
        expression::Expression,
        expression::Literal,
        intern,
        state::State,
        synthesize, synthesize_with_state,
        ty::{self, Type},
        variable::Variable,
    };

    fn intern<T>(value: T) -> intern::Intern<T>
    where
        T: Copy,
    {
        intern::Intern {
            index: 0, // This is not needed sometimes
            phantom: ::std::marker::PhantomData,
        }
    }

    #[test]
    fn lit_string()
    {
        assert_eq!(
            synthesize(Expression::Literal {
                literal: Literal::String("Foo"),
            }),
            Ok(Type::Literal {
                ty: ty::Literal::String
            })
        )
    }

    #[test]
    fn appl_string()
    {
        assert_eq!(
            synthesize(Expression::Application {
                function: Box::new(Expression::Abstraction {
                    parameter: "x",
                    body: Box::new(Expression::Variable { name: "x" }),
                }),
                argument: Box::new(Expression::Literal {
                    literal: Literal::String("Foo"),
                }),
            }),
            Ok(Type::Literal {
                ty: ty::Literal::String
            })
        )
    }

    #[test]
    fn appl_bool()
    {
        assert_eq!(
            synthesize(Expression::Application {
                function: Box::new(Expression::Abstraction {
                    parameter: "x",
                    body: Box::new(Expression::Variable { name: "x" }),
                }),
                argument: Box::new(Expression::Literal {
                    literal: Literal::Bool(true),
                }),
            }),
            Ok(Type::Literal {
                ty: ty::Literal::Bool
            })
        )
    }

    #[test]
    fn lambda()
    {
        assert_eq!(
            synthesize(Expression::Abstraction {
                parameter: "x",
                body: Box::new(Expression::Variable { name: "x" }),
            }),
            Ok(Type::Function {
                from: intern(Type::Existential {
                    id: Variable::Existential { id: 0 }
                }),
                to: intern(Type::Existential {
                    id: Variable::Existential { id: 0 }
                })
            })
        )
    }

    #[test]
    fn id_unit()
    {
        let mut state = State::initial();

        assert_eq!(
            synthesize_with_state(
                Expression::Application {
                    function: Box::new(Expression::Annotation {
                        expr: Box::new(Expression::Abstraction {
                            parameter: "x",
                            body: Box::new(Expression::Variable { name: "x" })
                        }),
                        ty: Type::Quantification {
                            variable: Variable::Named { name: "t" },
                            codomain: Type::Function {
                                from: Type::Variable {
                                    name: Variable::Named { name: "t" }
                                }
                                .store(&mut state),
                                to: Type::Variable {
                                    name: Variable::Named { name: "t" }
                                }
                                .store(&mut state)
                            }
                            .store(&mut state)
                        }
                    }),
                    argument: Box::new(Expression::Literal {
                        literal: Literal::String("Foo")
                    })
                },
                &mut state
            ),
            Ok(Type::Literal {
                ty: ty::Literal::String
            })
        )
    }

    #[test]
    fn tuples()
    {
        assert_eq!(
            synthesize(Expression::Tuple {
                first: Box::new(Expression::Literal {
                    literal: Literal::String("foo"),
                }),
                second: Box::new(Expression::Literal {
                    literal: Literal::Bool(true),
                }),
            }),
            Ok(Type::Product {
                left: intern(Type::Literal {
                    ty: ty::Literal::String
                }),
                right: intern(Type::Literal {
                    ty: ty::Literal::Bool
                })
            })
        )
    }

    #[test]
    fn tuples_in_lambda()
    {
        assert_eq!(
            synthesize(Expression::Application {
                function: Box::new(Expression::Abstraction {
                    parameter: "x",
                    body: Box::new(Expression::Tuple {
                        first: Box::new(Expression::Variable { name: "x" }),
                        second: Box::new(Expression::Variable { name: "x" }),
                    }),
                }),
                argument: Box::new(Expression::Literal {
                    literal: Literal::String("foo"),
                }),
            }),
            Ok(Type::Product {
                left: intern(Type::Literal {
                    ty: ty::Literal::String
                }),
                right: intern(Type::Literal {
                    ty: ty::Literal::String
                })
            })
        )
    }

    #[test]
    fn nested_tuples()
    {
        assert_eq!(
            synthesize(Expression::Application {
                function: Box::new(Expression::Abstraction {
                    parameter: "x",
                    body: Box::new(Expression::Tuple {
                        first: Box::new(Expression::Variable { name: "x" }),
                        second: Box::new(Expression::Tuple {
                            first: Box::new(Expression::Variable { name: "x" }),
                            second: Box::new(Expression::Variable { name: "x" }),
                        }),
                    }),
                }),
                argument: Box::new(Expression::Literal {
                    literal: Literal::String("foo"),
                }),
            }),
            Ok(Type::Product {
                left: intern(Type::Literal {
                    ty: ty::Literal::String
                }),
                right: intern(Type::Product {
                    left: intern(Type::Literal {
                        ty: ty::Literal::String
                    }),
                    right: intern(Type::Literal {
                        ty: ty::Literal::String
                    })
                })
            })
        )
    }

    #[test]
    fn tuples_in_fn()
    {
        let mut state = State::initial();

        assert_eq!(
            synthesize_with_state(
                Expression::Application {
                    function: Box::new(Expression::Annotation {
                        expr: Box::new(Expression::Abstraction {
                            parameter: "x",
                            body: Box::new(Expression::Variable { name: "x" })
                        }),
                        ty: Type::Quantification {
                            variable: Variable::Named { name: "t" },
                            codomain: Type::Function {
                                from: Type::Variable {
                                    name: Variable::Named { name: "t" }
                                }
                                .store(&mut state),
                                to: Type::Variable {
                                    name: Variable::Named { name: "t" }
                                }
                                .store(&mut state)
                            }
                            .store(&mut state)
                        }
                    }),
                    argument: Box::new(Expression::Tuple {
                        first: Box::new(Expression::Literal {
                            literal: Literal::String("foo")
                        }),
                        second: Box::new(Expression::Literal {
                            literal: Literal::Bool(true)
                        })
                    })
                },
                &mut state
            ),
            Ok(Type::Product {
                left: intern(Type::Literal {
                    ty: ty::Literal::String
                }),
                right: intern(Type::Literal {
                    ty: ty::Literal::String
                })
            })
        )
    }

    #[test]
    fn let_binding()
    {
        let mut state = State::initial();

        assert_eq!(
            synthesize_with_state(
                Expression::Let {
                    name: "a",
                    expr: Box::new(Expression::Literal {
                        literal: Literal::Bool(true)
                    }),
                    body: Box::new(Expression::Application {
                        function: Box::new(Expression::Annotation {
                            expr: Box::new(Expression::Abstraction {
                                parameter: "x",
                                body: Box::new(Expression::Variable { name: "x" })
                            }),
                            ty: Type::Quantification {
                                variable: Variable::Named { name: "t" },
                                codomain: Type::Function {
                                    from: Type::Variable {
                                        name: Variable::Named { name: "t" }
                                    }
                                    .store(&mut state),
                                    to: Type::Variable {
                                        name: Variable::Named { name: "t" }
                                    }
                                    .store(&mut state)
                                }
                                .store(&mut state)
                            }
                        }),
                        argument: Box::new(Expression::Variable { name: "a" })
                    })
                },
                &mut state
            ),
            Ok(Type::Literal {
                ty: ty::Literal::Bool
            })
        )
    }

    #[test]
    fn let_fn()
    {
        assert_eq!(
            synthesize(Expression::Application {
                function: Box::new(Expression::Let {
                    name: "newid",
                    expr: Box::new(Expression::Abstraction {
                        parameter: "x",
                        body: Box::new(Expression::Variable { name: "x" }),
                    }),
                    body: Box::new(Expression::Variable { name: "newid" }),
                }),
                argument: Box::new(Expression::Literal {
                    literal: Literal::String("Foo"),
                }),
            }),
            Ok(Type::Literal {
                ty: ty::Literal::String
            })
        )
    }

    #[test]
    fn generalised_let()
    {
        let mut state = State::initial();

        assert_eq!(
            synthesize_with_state(
                Expression::Let {
                    name: "newid",
                    expr: Box::new(Expression::Annotation {
                        expr: Box::new(Expression::Abstraction {
                            parameter: "x",
                            body: Box::new(Expression::Variable { name: "x" })
                        }),
                        ty: Type::Quantification {
                            variable: Variable::Named { name: "t" },
                            codomain: Type::Function {
                                from: Type::Variable {
                                    name: Variable::Named { name: "t" }
                                }
                                .store(&mut state),
                                to: Type::Variable {
                                    name: Variable::Named { name: "t" }
                                }
                                .store(&mut state)
                            }
                            .store(&mut state)
                        }
                    }),
                    body: Box::new(Expression::Tuple {
                        first: Box::new(Expression::Application {
                            function: Box::new(Expression::Variable { name: "newid" }),
                            argument: Box::new(Expression::Literal {
                                literal: Literal::String("foo")
                            })
                        }),
                        second: Box::new(Expression::Application {
                            function: Box::new(Expression::Variable { name: "newid" }),
                            argument: Box::new(Expression::Literal {
                                literal: Literal::Bool(true)
                            })
                        })
                    })
                },
                &mut state
            ),
            Ok(Type::Product {
                left: intern(Type::Literal {
                    ty: ty::Literal::String
                }),
                right: intern(Type::Literal {
                    ty: ty::Literal::Bool
                })
            })
        )
    }
}
