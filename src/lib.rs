#![feature(box_syntax)]
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

fn substitute(a: ty::Type, alpha: &str, b: ty::Type, state: &mut state::State) -> ty::Type
{
    match a {
        ty::Type::Variable { name } => {
            if name == alpha {
                b
            } else {
                a
            }
        }
        ty::Type::Function { from, to } => ty::Type::Function {
            from: substitute(from.fetch(state), alpha, b, state).store(state),
            to: substitute(to.fetch(state), alpha, b, state).store(state),
        },
        _ => unimplemented!("{:?}", a),
    }
}

fn subtype<'ctx>(
    a: &ty::Type,
    b: &ty::Type,
    state: &mut state::State,
    context: &'ctx mut context::Context,
) -> ::std::result::Result<&'ctx mut context::Context, context::Error>
{
    match (a, b) {
        (ty::Type::Variable { name: alpha1 }, ty::Type::Variable { name: alpha2 }) => {
            assert!(a.is_well_formed(state, context));
            assert_eq!(alpha1, alpha2);

            Ok(context)
        }
        (ty::Type::Existential { id }, _) => {
            if !b.has_existential(*id, state) {
                instantiate_l(*id, b, state, context)
            } else {
                unimplemented!()
            }
        }
        (_, ty::Type::Existential { id }) => {
            if !a.has_existential(*id, state) {
                instantiate_r(a, *id, state, context)
            } else {
                unimplemented!()
            }
        }
        _ => unimplemented!("{:?}", (a, b)),
    }
}

fn instantiate_l<'ctx>(
    alpha: u64,
    b: &ty::Type,
    state: &mut state::State,
    context: &'ctx mut context::Context,
) -> ::std::result::Result<&'ctx mut context::Context, context::Error>
{
    let (mut left_context, right_context) =
        context.split_at(context::Element::Existential { id: alpha }, state)?;

    if b.is_monotype(state) && b.is_well_formed(state, &mut left_context) {
        return context.insert_in_place(
            context::Element::Existential { id: alpha },
            [context::Element::Solved {
                id: alpha,
                ty: b.store(state),
            }],
            state,
        );
    }

    match b {
        &ty::Type::Existential { id } => {
            return context.insert_in_place(
                context::Element::Existential { id },
                [context::Element::Solved {
                    id,
                    ty: ty::Type::Existential { id: alpha }.store(state),
                }],
                state,
            );
        }
        _ => unimplemented!(),
    }
}

fn instantiate_r<'ctx>(
    a: &ty::Type,
    alpha: u64,
    state: &mut state::State,
    context: &'ctx mut context::Context,
) -> ::std::result::Result<&'ctx mut context::Context, context::Error>
{
    let (mut left_context, right_context) =
        context.split_at(context::Element::Existential { id: alpha }, state)?;

    if a.is_monotype(state) && a.is_well_formed(state, &mut left_context) {
        return context.insert_in_place(
            context::Element::Existential { id: alpha },
            [context::Element::Solved {
                id: alpha,
                ty: a.store(state),
            }],
            state,
        );
    }

    unimplemented!()
}

fn synthesize_with_state(expression: expression::Expression, state: &mut state::State) -> ty::Type
{
    let mut context = context::Context::initial();
    // NOTE: This unwrap is temporary until proper error
    // handling has been implemented for the whole crate
    let (ty, new_context) = expression.synthesize(state, &mut context).unwrap();

    ty.apply_context(state, new_context)
}

fn synthesize(expression: expression::Expression) -> ty::Type
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
            Type::Literal {
                ty: ty::Literal::String
            }
        )
    }

    #[test]
    fn appl_string()
    {
        assert_eq!(
            synthesize(Expression::Application {
                function: box Expression::Abstraction {
                    parameter: "x",
                    body: box Expression::Variable { name: "x" }
                },
                argument: box Expression::Literal {
                    literal: Literal::String("Foo"),
                }
            }),
            Type::Literal {
                ty: ty::Literal::String
            }
        )
    }

    #[test]
    fn appl_bool()
    {
        assert_eq!(
            synthesize(Expression::Application {
                function: box Expression::Abstraction {
                    parameter: "x",
                    body: box Expression::Variable { name: "x" }
                },
                argument: box Expression::Literal {
                    literal: Literal::Bool(true)
                }
            }),
            Type::Literal {
                ty: ty::Literal::Bool
            }
        )
    }

    #[test]
    fn lambda()
    {
        assert_eq!(
            synthesize(Expression::Abstraction {
                parameter: "x",
                body: box Expression::Variable { name: "x" }
            }),
            Type::Function {
                from: intern(Type::Existential { id: 0 }),
                to: intern(Type::Existential { id: 0 })
            }
        )
    }

    #[test]
    fn id_unit()
    {
        let mut state = State::initial();

        assert_eq!(
            synthesize_with_state(
                Expression::Application {
                    function: box Expression::Annotation {
                        expr: box Expression::Abstraction {
                            parameter: "x",
                            body: box Expression::Variable { name: "x" }
                        },
                        ty: Type::Quantification {
                            variable: "t",
                            codomain: Type::Function {
                                from: Type::Variable { name: "t" }.store(&mut state),
                                to: Type::Variable { name: "t" }.store(&mut state)
                            }
                            .store(&mut state)
                        }
                    },
                    argument: box Expression::Literal {
                        literal: Literal::String("Foo")
                    }
                },
                &mut state
            ),
            Type::Literal {
                ty: ty::Literal::String
            }
        )
    }

    #[test]
    fn tuples()
    {
        assert_eq!(
            synthesize(Expression::Tuple {
                first: box Expression::Literal {
                    literal: Literal::String("foo")
                },
                second: box Expression::Literal {
                    literal: Literal::Bool(true)
                }
            }),
            Type::Product {
                left: intern(Type::Literal {
                    ty: ty::Literal::String
                }),
                right: intern(Type::Literal {
                    ty: ty::Literal::Bool
                })
            }
        )
    }

    #[test]
    fn tuples_in_lambda()
    {
        assert_eq!(
            synthesize(Expression::Application {
                function: box Expression::Abstraction {
                    parameter: "x",
                    body: box Expression::Tuple {
                        first: box Expression::Variable { name: "x" },
                        second: box Expression::Variable { name: "x" }
                    }
                },
                argument: box Expression::Literal {
                    literal: Literal::String("foo")
                }
            }),
            Type::Product {
                left: intern(Type::Literal {
                    ty: ty::Literal::String
                }),
                right: intern(Type::Literal {
                    ty: ty::Literal::String
                })
            }
        )
    }

    #[test]
    fn nested_tuples()
    {
        assert_eq!(
            synthesize(Expression::Application {
                function: box Expression::Abstraction {
                    parameter: "x",
                    body: box Expression::Tuple {
                        first: box Expression::Variable { name: "x" },
                        second: box Expression::Tuple {
                            first: box Expression::Variable { name: "x" },
                            second: box Expression::Variable { name: "x" }
                        }
                    }
                },
                argument: box Expression::Literal {
                    literal: Literal::String("foo")
                }
            }),
            Type::Product {
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
            }
        )
    }

    #[test]
    fn tuples_in_fn()
    {
        let mut state = State::initial();

        assert_eq!(
            synthesize_with_state(
                Expression::Application {
                    function: box Expression::Annotation {
                        expr: box Expression::Abstraction {
                            parameter: "x",
                            body: box Expression::Variable { name: "x" }
                        },
                        ty: Type::Quantification {
                            variable: "t",
                            codomain: Type::Function {
                                from: Type::Variable { name: "t" }.store(&mut state),
                                to: Type::Variable { name: "t" }.store(&mut state)
                            }
                            .store(&mut state)
                        }
                    },
                    argument: box Expression::Tuple {
                        first: box Expression::Literal {
                            literal: Literal::String("foo")
                        },
                        second: box Expression::Literal {
                            literal: Literal::Bool(true)
                        }
                    }
                },
                &mut state
            ),
            Type::Product {
                left: intern(Type::Literal {
                    ty: ty::Literal::String
                }),
                right: intern(Type::Literal {
                    ty: ty::Literal::String
                })
            }
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
                    expr: box Expression::Literal {
                        literal: Literal::Bool(true)
                    },
                    body: box Expression::Application {
                        function: box Expression::Annotation {
                            expr: box Expression::Abstraction {
                                parameter: "x",
                                body: box Expression::Variable { name: "x" }
                            },
                            ty: Type::Quantification {
                                variable: "t",
                                codomain: Type::Function {
                                    from: Type::Variable { name: "t" }.store(&mut state),
                                    to: Type::Variable { name: "t" }.store(&mut state)
                                }
                                .store(&mut state)
                            }
                        },
                        argument: box Expression::Variable { name: "a" }
                    }
                },
                &mut state
            ),
            Type::Literal {
                ty: ty::Literal::Bool
            }
        )
    }

    #[test]
    fn let_fn()
    {
        assert_eq!(
            synthesize(Expression::Application {
                function: box Expression::Let {
                    name: "newid",
                    expr: box Expression::Abstraction {
                        parameter: "x",
                        body: box Expression::Variable { name: "x" }
                    },
                    body: box Expression::Variable { name: "newid" }
                },
                argument: box Expression::Literal {
                    literal: Literal::String("Foo")
                }
            }),
            Type::Literal {
                ty: ty::Literal::String
            }
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
                    expr: box Expression::Annotation {
                        expr: box Expression::Abstraction {
                            parameter: "x",
                            body: box Expression::Variable { name: "x" }
                        },
                        ty: Type::Quantification {
                            variable: "t",
                            codomain: Type::Function {
                                from: Type::Variable { name: "t" }.store(&mut state),
                                to: Type::Variable { name: "t" }.store(&mut state)
                            }
                            .store(&mut state)
                        }
                    },
                    body: box Expression::Tuple {
                        first: box Expression::Application {
                            function: box Expression::Variable { name: "newid" },
                            argument: box Expression::Literal {
                                literal: Literal::String("foo")
                            }
                        },
                        second: box Expression::Application {
                            function: box Expression::Variable { name: "newid" },
                            argument: box Expression::Literal {
                                literal: Literal::Bool(true)
                            }
                        }
                    }
                },
                &mut state
            ),
            Type::Product {
                left: intern(Type::Literal {
                    ty: ty::Literal::String
                }),
                right: intern(Type::Literal {
                    ty: ty::Literal::Bool
                })
            }
        )
    }
}
