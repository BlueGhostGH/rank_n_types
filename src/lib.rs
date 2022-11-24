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

use std::marker::PhantomData;

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

            Expression::Variable { name } => match context.fetch_annotation(name, state) {
                Some(annotation) => (annotation, context),
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
                        ty: Type::Existential { id: alpha }.store(state),
                    });

                let delta = body
                    .checks_against(&Type::Existential { id: beta }, state, gamma)
                    .drain_until(ContextElement::TypedVariable {
                        name: parameter,
                        ty: Type::Existential { id: alpha }.store(state),
                    });

                (
                    Type::Function {
                        from: Type::Existential { id: alpha }.store(state),
                        to: Type::Existential { id: beta }.store(state),
                    },
                    delta,
                )
            }

            Expression::Application { function, argument } => {
                let (a, theta) = function.synthesize(state, context);

                argument.application_synthesize(&a.apply_context(theta, state), state, theta)
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
                let delta = self.checks_against(&from.fetch(state), state, context);
                return (to.fetch(state), delta);
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
        assert!(ty.is_well_formed(&context, state));
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

                let a = a.apply_context(theta, state);
                let b = ty.apply_context(theta, state);
                subtype(state, theta, &a, &b)
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum LiteralType {
    String,
}

#[derive(Debug, Eq, Clone, Copy)]
struct Index<T> {
    index: usize,
    phantom: PhantomData<T>,
}

trait Store<T>
where
    T: Copy,
{
    fn fetch(&self, index: Index<T>) -> T;
    fn store(&mut self, value: T) -> Index<T>;
}

impl<T> Index<T>
where
    T: Copy,
{
    fn fetch<S>(&self, state: &S) -> T
    where
        S: Store<T>,
    {
        state.fetch(*self)
    }
}

impl<T> PartialEq for Index<T> {
    fn eq(&self, _other: &Self) -> bool {
        // NOTE: We don't care about the index, just the value it points to
        true
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Type {
    Literal {
        ty: LiteralType,
    },
    Existential {
        id: u64,
    },
    Function {
        from: Index<Type>,
        to: Index<Type>,
    },
    Quantification {
        variable_name: &'static str,
        codomain: Index<Type>,
    },
    Product {
        left: Index<Type>,
        right: Index<Type>,
    },
}

impl Type {
    fn store(self, state: &mut State) -> Index<Self> {
        let index = state.types.len();
        state.types.push(self);

        Index {
            index,
            phantom: PhantomData,
        }
    }

    fn apply_context(self, context: &Context, state: &mut State) -> Self {
        match self {
            Type::Literal { .. } => self,
            Type::Function { from, to } => Type::Function {
                from: from.fetch(state).apply_context(context, state).store(state),
                to: to.fetch(state).apply_context(context, state).store(state),
            },
            Type::Quantification {
                variable_name,
                codomain,
            } => Type::Quantification {
                variable_name,
                codomain: codomain
                    .fetch(state)
                    .apply_context(context, state)
                    .store(state),
            },
            Type::Existential { id } => {
                if let Some(tau) = context.fetch_solved(id, state) {
                    tau.apply_context(context, state)
                } else {
                    self
                }
            }
            Type::Product { left, right } => Type::Product {
                left: left.fetch(state).apply_context(context, state).store(state),
                right: right
                    .fetch(state)
                    .apply_context(context, state)
                    .store(state),
            },
        }
    }

    fn is_well_formed(&self, context: &Context, state: &State) -> bool {
        match self {
            Type::Literal { .. } => true,
            Type::Function { from, to } => {
                from.fetch(state).is_well_formed(context, state)
                    && to.fetch(state).is_well_formed(context, state)
            }
            Type::Quantification {
                variable_name,
                codomain,
            } => unimplemented!(),
            Type::Existential { id } => {
                context.has_existential(*id) || context.fetch_solved(*id, state).is_some()
            }
            Type::Product { left, right } => {
                left.fetch(state).is_well_formed(context, state)
                    && right.fetch(state).is_well_formed(context, state)
            }
        }
    }

    fn is_monotype(&self, state: &State) -> bool {
        match self {
            Type::Quantification { .. } => false,
            Type::Function { from, to } => {
                from.fetch(state).is_monotype(state) && to.fetch(state).is_monotype(state)
            }
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum ContextElement {
    Existential { id: u64 },
    Solved { id: u64, ty: Index<Type> },
    TypedVariable { name: &'static str, ty: Index<Type> },
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

                let left_context = {
                    let elements = lhs.to_vec();
                    Context { elements }
                };
                let right_context = {
                    let elements = rhs.to_vec();
                    Context { elements }
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

    fn fetch_solved(&self, alpha: u64, state: &State) -> Option<Type> {
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
            .map(|(_, ty)| ty.fetch(state))
    }

    fn fetch_annotation(&self, variable_name: &str, state: &State) -> Option<Type> {
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
            .map(|(_, ty)| ty.fetch(state))
    }
}

#[derive(Debug)]
struct State {
    existentials_count: u64,
    types: Vec<Type>,
}

impl State {
    fn initial() -> Self {
        State {
            existentials_count: 0,
            types: Vec::new(),
        }
    }

    fn fresh_existential(&mut self) -> u64 {
        let existential = self.existentials_count;
        self.existentials_count += 1;

        existential
    }
}

impl Store<Type> for State {
    fn fetch(&self, Index { index, .. }: Index<Type>) -> Type {
        self.types[index]
    }

    fn store(&mut self, value: Type) -> Index<Type> {
        let index = self.types.len();
        self.types.push(value);

        Index {
            index,
            phantom: PhantomData,
        }
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
    state: &mut State,
    context: &'ctx mut Context,
    alpha: u64,
    b: &Type,
) -> &'ctx mut Context {
    let (left_context, right_context) = context.split_at(ContextElement::Existential { id: alpha });

    if b.is_monotype(state) && b.is_well_formed(&left_context, state) {
        return context.insert_in_place(
            ContextElement::Existential { id: alpha },
            [ContextElement::Solved {
                id: alpha,
                ty: b.store(state),
            }],
        );
    }

    match b {
        &Type::Existential { id } => {
            return context.insert_in_place(
                ContextElement::Existential { id },
                [ContextElement::Solved {
                    id,
                    ty: Type::Existential { id: alpha }.store(state),
                }],
            );
        }
        _ => unimplemented!(),
    }
}

fn instantiate_r<'ctx>(
    state: &mut State,
    context: &'ctx mut Context,
    a: &Type,
    alpha: u64,
) -> &'ctx mut Context {
    let (left_context, right_context) = context.split_at(ContextElement::Existential { id: alpha });

    if a.is_monotype(state) && a.is_well_formed(&left_context, state) {
        return context.insert_in_place(
            ContextElement::Existential { id: alpha },
            [ContextElement::Solved {
                id: alpha,
                ty: a.store(state),
            }],
        );
    }

    unimplemented!()
}

fn synthesize(expression: Expression) -> Type {
    let mut state = State::initial();
    let mut context = Context::initial();
    let (ty, new_context) = expression.synthesize(&mut state, &mut context);

    ty.apply_context(&new_context, &mut state)
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
