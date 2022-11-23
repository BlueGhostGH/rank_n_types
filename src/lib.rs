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
    Literal {
        literal: Literal,
    },
    Variable {
        name: &'static str,
    },
    Application {
        function: Box<Expression>,
        argument: Box<Expression>,
    },
    Abstraction {
        parameter: &'static str,
        body: Box<Expression>,
    },
    Tuple {
        first: Box<Expression>,
        second: Box<Expression>,
    },
}

impl Expression {
    fn synthesize<'ctx>(
        &self,
        state: &mut State,
        context: &'ctx mut Context,
    ) -> (Type, &'ctx mut Context) {
        match self {
            Expression::Literal { literal } => (
                Type::Literal {
                    ty: literal.synthesize(),
                },
                context,
            ),

            Expression::Variable { name } => match context.get_annotation(name) {
                Some(annotation) => (annotation.clone(), context),
                None => unreachable!(),
            },

            Expression::Abstraction { parameter, body } => {
                let alpha = state.fresh_existential();
                let beta = state.fresh_existential();

                let gamma = context
                    .push(ContextElement::Existential { id: alpha })
                    .push(ContextElement::Existential { id: beta })
                    .push(ContextElement::TypedVariable {
                        name: parameter,
                        ty: Type::Existential { id: alpha },
                    });
                let delta = body
                    .checks_against(&Type::Existential { id: beta }, state, gamma)
                    .drain_until(ContextElement::TypedVariable {
                        name: parameter,
                        ty: Type::Existential { id: alpha },
                    });

                (
                    Type::Function {
                        from: box Type::Existential { id: alpha },
                        to: box Type::Existential { id: beta },
                    },
                    delta,
                )
            }

            Expression::Application { function, argument } => {
                let (a, theta) = function.synthesize(state, context);

                argument.application_synthesize(&a.apply_context(theta), state, theta)
            }

            _ => unimplemented!(),
        }
    }

    fn application_synthesize<'ctx>(
        &self,
        ty: &Type,
        state: &mut State,
        context: &'ctx mut Context,
    ) -> (Type, &'ctx mut Context) {
        match ty {
            Type::Function { from, to } => {
                let delta = self.checks_against(from, state, context);
                return (*to.clone(), delta);
            }
            _ => unreachable!(),
        }
    }

    fn checks_against<'ctx>(
        &self,
        ty: &Type,
        state: &mut State,
        context: &'ctx mut Context,
    ) -> &'ctx mut Context {
        // assert!(ty.is_well_formed(&context));
        match (self, &ty) {
            (Expression::Literal { literal }, Type::Literal { ty }) => unimplemented!(),
            (Expression::Abstraction { parameter, body }, Type::Function { from, to }) => {
                unimplemented!()
            }
            (
                _,
                Type::Quantification {
                    variable_name,
                    codomain,
                },
            ) => unimplemented!(),
            (Expression::Tuple { first, second }, Type::Product { left, right }) => {
                unimplemented!()
            }
            (_, _) => {
                let (a, theta) = self.synthesize(state, context);
                subtype(
                    state,
                    theta,
                    &a.apply_context(&theta),
                    &ty.clone().apply_context(&theta),
                )
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum LiteralType {
    String,
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum Type {
    Literal {
        ty: LiteralType,
    },
    Existential {
        id: u64,
    },
    Function {
        from: Box<Type>,
        to: Box<Type>,
    },
    Quantification {
        variable_name: &'static str,
        codomain: Box<Type>,
    },
    Product {
        left: Box<Type>,
        right: Box<Type>,
    },
}

impl Type {
    fn apply_context(self, context: &Context) -> Self {
        match self {
            Type::Literal { .. } => self,
            Type::Function { from, to } => Type::Function {
                from: box from.apply_context(context),
                to: box to.apply_context(context),
            },
            Type::Quantification {
                variable_name,
                codomain,
            } => Type::Quantification {
                variable_name,
                codomain: box codomain.apply_context(context),
            },
            Type::Existential { id } => {
                if let Some(tau) = context.fetch_solved(id) {
                    tau.clone().apply_context(context)
                } else {
                    self
                }
            }
            Type::Product { left, right } => Type::Product {
                left: box left.apply_context(context),
                right: box right.apply_context(context),
            },
        }
    }

    fn is_well_formed(&self, context: &Context) -> bool {
        match self {
            Type::Literal { .. } => true,
            Type::Function { from, to } => {
                from.is_well_formed(context) && to.is_well_formed(context)
            }
            Type::Quantification {
                variable_name,
                codomain,
            } => unimplemented!(),
            Type::Existential { id } => {
                context.has_existential(*id) || context.fetch_solved(*id).is_some()
            }
            Type::Product { left, right } => {
                left.is_well_formed(context) && right.is_well_formed(context)
            }
        }
    }

    fn is_monotype(&self) -> bool {
        match self {
            Type::Quantification { .. } => false,
            Type::Function { from, to } => from.is_monotype() && to.is_monotype(),
            _ => true,
        }
    }

    fn existential_occurs(&self, alpha: u64) -> bool {
        match self {
            Type::Literal { .. } => false,
            Type::Existential { id } => &alpha == id,
            _ => unimplemented!(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum ContextElement {
    Existential { id: u64 },
    Solved { id: u64, ty: Type },
    TypedVariable { name: &'static str, ty: Type },
}

#[derive(Debug)]
struct Context {
    elements: Vec<ContextElement>,
}

impl Context {
    fn initial() -> Self {
        Context {
            elements: Vec::new(),
        }
    }

    fn push(&mut self, element: ContextElement) -> &mut Self {
        self.elements.push(element);

        self
    }

    fn insert_in_place<const N: usize>(
        &mut self,
        element: ContextElement,
        inserts: [ContextElement; N],
    ) -> &mut Self {
        match self.elements.iter().position(|elem| elem == &element) {
            Some(index) => {
                let _count = self.elements.splice(index..=index, inserts).count();
            }
            None => unreachable!("{:?}", (&self.elements, element)),
        };

        self
    }

    fn drain_until(&mut self, element: ContextElement) -> &mut Self {
        match self.elements.iter().position(|elem| elem == &element) {
            Some(index) => {
                let _drained = self.elements.drain(index..);
            }
            None => unreachable!(),
        };

        self
    }

    fn split_at(&mut self, element: ContextElement) -> (Self, Self) {
        match self.elements.iter().position(|elem| elem == &element) {
            Some(index) => {
                let (lhs, rhs) = self.elements.split_at(index);

                let left_context = Context {
                    elements: lhs.to_vec(),
                };
                let right_context = Context {
                    elements: rhs.to_vec(),
                };

                (left_context, right_context)
            }
            None => unreachable!(),
        }
    }

    fn has_existential(&self, alpha: u64) -> bool {
        self.elements
            .iter()
            .any(|elem| elem == &ContextElement::Existential { id: alpha })
    }

    fn fetch_solved(&self, alpha: u64) -> Option<&Type> {
        self.elements
            .iter()
            .filter_map(|elem| {
                if let ContextElement::Solved { id, ty } = elem {
                    Some((id, ty))
                } else {
                    None
                }
            })
            .find(|(id, _)| id == &&alpha)
            .map(|(_, ty)| ty)
    }

    fn get_annotation(&self, variable_name: &str) -> Option<&Type> {
        self.elements
            .iter()
            .filter_map(|elem| {
                if let ContextElement::TypedVariable { name, ty } = elem {
                    Some((name, ty))
                } else {
                    None
                }
            })
            .find(|(name, _)| name == &&variable_name)
            .map(|(_, ty)| ty)
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

    fn fresh_existential(&mut self) -> u64 {
        let existential = self.existentials_count;
        self.existentials_count += 1;

        existential
    }
}

fn subtype<'ctx>(
    state: &mut State,
    context: &'ctx mut Context,
    a: &Type,
    b: &Type,
) -> &'ctx mut Context {
    match (a, b) {
        (Type::Existential { id }, _) => {
            if !b.existential_occurs(*id) {
                instantiate_l(state, context, *id, b)
            } else {
                unimplemented!()
            }
        }
        (_, Type::Existential { id }) => {
            if !a.existential_occurs(*id) {
                instantiate_r(state, context, a, *id)
            } else {
                unimplemented!()
            }
        }
        _ => unimplemented!(),
    }
}

fn instantiate_l<'ctx>(
    _state: &mut State,
    context: &'ctx mut Context,
    alpha: u64,
    b: &Type,
) -> &'ctx mut Context {
    let (left_context, right_context) = context.split_at(ContextElement::Existential { id: alpha });

    if b.is_monotype() && b.is_well_formed(&left_context) {
        return context.insert_in_place(
            ContextElement::Existential { id: alpha },
            [ContextElement::Solved {
                id: alpha,
                ty: b.clone(),
            }],
        );
    }

    match b {
        &Type::Existential { id } => {
            return context.insert_in_place(
                ContextElement::Existential { id },
                [ContextElement::Solved {
                    id,
                    ty: Type::Existential { id: alpha },
                }],
            );
        }
        _ => unimplemented!(),
    }
}

fn instantiate_r<'ctx>(
    _state: &mut State,
    context: &'ctx mut Context,
    a: &Type,
    alpha: u64,
) -> &'ctx mut Context {
    let (left_context, right_context) = context.split_at(ContextElement::Existential { id: alpha });

    if a.is_monotype() && a.is_well_formed(&left_context) {
        return context.insert_in_place(
            ContextElement::Existential { id: alpha },
            [ContextElement::Solved {
                id: alpha,
                ty: a.clone(),
            }],
        );
    }

    unimplemented!()
}

fn synthesize(expression: Expression) -> Type {
    let mut state = State::initial();
    let mut context = Context::initial();
    let (ty, new_context) = expression.synthesize(&mut state, &mut context);

    ty.apply_context(&new_context)
}

#[cfg(test)]
mod tests {
    use crate::{synthesize, Expression, Literal, LiteralType, Type};

    #[test]
    fn lit_string() {
        assert_eq!(
            synthesize(Expression::Literal {
                literal: Literal::String("Foo"),
            }),
            Type::Literal {
                ty: LiteralType::String
            }
        )
    }

    #[test]
    fn appl_string() {
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
                ty: LiteralType::String
            }
        )
    }
}
