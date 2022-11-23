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

#[derive(Debug)]
enum Literal {
    String(&'static str),
}

impl Literal {
    fn synthesize(&self) -> LiteralType {
        match self {
            Literal::String(_) => LiteralType::String,
        }
    }
}

#[derive(Debug)]
enum Expression {
    Literal { literal: Literal },
}

impl Expression {
    fn synthesize(&self, _state: &mut State, context: &Context) -> (Type, Context) {
        match self {
            Expression::Literal { literal } => (
                Type::Literal {
                    ty: literal.synthesize(),
                },
                context.clone(),
            ),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum LiteralType {
    String,
}

#[derive(Debug, PartialEq, Eq)]
enum Type {
    Literal { ty: LiteralType },
}

impl Type {
    fn apply_context(self, _context: &Context) -> Self {
        match self {
            Type::Literal { .. } => self,
        }
    }
}

#[derive(Debug, Clone)]
enum ContextElement {}

#[derive(Debug, Clone)]
struct Context {
    elements: Vec<ContextElement>,
}

impl Context {
    fn initial() -> Self {
        Context {
            elements: Vec::new(),
        }
    }
}

#[derive(Debug)]
struct State {
    existentials_count: u64,
}

impl State {
    fn initial() -> Self {
        State {
            existentials_count: 0,
        }
    }
}

fn synthetize(expression: Expression) -> Type {
    let (ty, new_context) = expression.synthesize(&mut State::initial(), &Context::initial());

    ty.apply_context(&new_context)
}

fn string_literal(content: &'static str) -> Expression {
    Expression::Literal {
        literal: Literal::String(content),
    }
}

#[cfg(test)]
mod tests {
    use crate::{string_literal, synthetize, LiteralType, Type};

    #[test]
    fn lit_string() {
        assert_eq!(
            synthetize(string_literal("Foo")),
            Type::Literal {
                ty: LiteralType::String
            }
        )
    }
}
