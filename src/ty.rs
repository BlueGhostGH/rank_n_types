use crate::{context, expression, intern, state, variable};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum Literal
{
    Unit,
    Bool,
    Int,
    Float,
    Char,
    String,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum Type
{
    Literal
    {
        ty: Literal
    },
    Product
    {
        left: intern::Intern<Type>,
        right: intern::Intern<Type>,
    },
    Variable
    {
        name: variable::Variable
    },
    Existential
    {
        id: variable::Variable
    },
    Quantification
    {
        variable: variable::Variable,
        codomain: intern::Intern<Type>,
    },
    Function
    {
        from: intern::Intern<Type>,
        to: intern::Intern<Type>,
    },
}

impl Type
{
    pub(crate) fn store(self, state: &mut state::State) -> intern::Intern<Self>
    {
        let index = state.types.len();
        state.types.push(self);

        intern::Intern {
            index,
            phantom: ::std::marker::PhantomData,
        }
    }

    pub(crate) fn synthesize_application<'ctx>(
        &self,
        expr: &expression::Expression,
        state: &mut state::State,
        context: &'ctx mut context::Context,
    ) -> ::std::result::Result<(Type, &'ctx mut context::Context), crate::error::Error>
    {
        match self {
            &Type::Existential { id } => {
                let alpha = state.fresh_existential();
                let beta = state.fresh_existential();

                let gamma = context.insert_in_place(
                    context::Element::Existential { id },
                    [
                        context::Element::Existential { id: beta },
                        context::Element::Existential { id: alpha },
                        context::Element::SolvedExistential {
                            id,
                            ty: Type::Function {
                                from: Type::Existential { id: alpha }.store(state),
                                to: Type::Existential { id: beta }.store(state),
                            }
                            .store(state),
                        },
                    ],
                    state,
                );
                let delta =
                    expr.checks_against(&Type::Existential { id: alpha }, state, context)?;

                Ok((Type::Existential { id: beta }, delta))
            }
            Type::Quantification { variable, codomain } => {
                let alpha = state.fresh_existential();
                let gamma = context.push(context::Element::Existential { id: alpha });
                let substituted_a = codomain.fetch(state).substitute(
                    variable,
                    &Type::Existential { id: alpha },
                    state,
                );

                substituted_a.synthesize_application(expr, state, gamma)
            }
            Type::Function { from, to } => {
                let delta = expr.checks_against(&from.fetch(state), state, context)?;

                Ok((to.fetch(state), delta))
            }
            _ => Err(Error::InvalidApplication {
                kind: Kind::from(*self),
            })?,
        }
    }

    pub(crate) fn apply_context(self, state: &mut state::State, context: &context::Context)
        -> Self
    {
        match self {
            Type::Literal { .. } => self,
            Type::Product { left, right } => Type::Product {
                left: left.fetch(state).apply_context(state, context).store(state),
                right: right
                    .fetch(state)
                    .apply_context(state, context)
                    .store(state),
            },
            Type::Variable { .. } => self,
            Type::Existential { id } => {
                if let Some(tau) = context.fetch_solved(&id, state) {
                    tau.apply_context(state, context)
                } else {
                    self
                }
            }
            Type::Quantification {
                variable: variable_name,
                codomain,
            } => Type::Quantification {
                variable: variable_name,
                codomain: codomain
                    .fetch(state)
                    .apply_context(state, context)
                    .store(state),
            },
            Type::Function { from, to } => Type::Function {
                from: from.fetch(state).apply_context(state, context).store(state),
                to: to.fetch(state).apply_context(state, context).store(state),
            },
        }
    }

    pub(crate) fn substitute(
        &self,
        alpha: &variable::Variable,
        ty: &Type,
        state: &mut state::State,
    ) -> Self
    {
        match self {
            Type::Literal { .. } => *self,
            Type::Product { left, right } => Type::Product {
                left: left.fetch(state).substitute(alpha, ty, state).store(state),
                right: right.fetch(state).substitute(alpha, ty, state).store(state),
            },
            Type::Variable { name } => {
                if name == alpha {
                    *ty
                } else {
                    *self
                }
            }
            Type::Existential { id } => {
                if id == alpha {
                    *ty
                } else {
                    *self
                }
            }
            Type::Quantification { variable, codomain } => {
                if variable == alpha {
                    Type::Quantification {
                        variable: *variable,
                        codomain: ty.store(state),
                    }
                } else {
                    Type::Quantification {
                        variable: *variable,
                        codomain: codomain
                            .fetch(state)
                            .substitute(alpha, ty, state)
                            .store(state),
                    }
                }
            }
            Type::Function { from, to } => Type::Function {
                from: from.fetch(state).substitute(alpha, ty, state).store(state),
                to: to.fetch(state).substitute(alpha, ty, state).store(state),
            },
        }
    }

    pub(crate) fn is_well_formed(
        &self,
        state: &state::State,
        context: &mut context::Context,
    ) -> bool
    {
        match self {
            Type::Literal { .. } => true,
            Type::Product { left, right } => {
                left.fetch(state).is_well_formed(state, context)
                    && right.fetch(state).is_well_formed(state, context)
            }
            Type::Variable { name } => context.has_variable(name),
            Type::Existential { id } => {
                context.has_existential(id) || context.fetch_solved(id, state).is_some()
            }
            Type::Quantification { variable, codomain } => codomain.fetch(state).is_well_formed(
                state,
                context.push(context::Element::Variable { name: *variable }),
            ),
            Type::Function { from, to } => {
                from.fetch(state).is_well_formed(state, context)
                    && to.fetch(state).is_well_formed(state, context)
            }
        }
    }

    pub(crate) fn is_monotype(&self, state: &state::State) -> bool
    {
        match self {
            Type::Quantification { .. } => false,
            Type::Function { from, to } => {
                from.fetch(state).is_monotype(state) && to.fetch(state).is_monotype(state)
            }
            _ => true,
        }
    }

    pub(crate) fn has_existential(&self, alpha: &variable::Variable, state: &state::State) -> bool
    {
        match self {
            Type::Literal { .. } => false,
            Type::Product { left, right } => {
                let occurs_in_left = left.fetch(state).has_existential(alpha, state);
                let occurs_in_right = right.fetch(state).has_existential(alpha, state);

                occurs_in_left || occurs_in_right
            }
            Type::Variable { name } => name == alpha,
            Type::Existential { id } => id == alpha,
            Type::Quantification { variable, codomain } => match (alpha, variable) {
                (
                    variable::Variable::Existential { id: alpha },
                    variable::Variable::Existential { id: beta },
                ) => alpha == beta,
                (_, _) => codomain.fetch(state).has_existential(alpha, state),
            },
            Type::Function { from, to } => {
                let occurs_in_from = from.fetch(state).has_existential(alpha, state);
                let occurs_in_to = to.fetch(state).has_existential(alpha, state);

                occurs_in_from || occurs_in_to
            }
        }
    }
}

pub(crate) fn subtype<'ctx>(
    a: &Type,
    b: &Type,
    state: &mut state::State,
    context: &'ctx mut context::Context,
) -> ::std::result::Result<&'ctx mut context::Context, crate::error::Error>
{
    assert!(a.is_well_formed(state, context));
    assert!(b.is_well_formed(state, context));

    match (a, b) {
        (Type::Literal { ty: t0 }, Type::Literal { ty: t1 }) => {
            assert_eq!(t0, t1);

            Ok(context)
        }
        (
            Type::Product {
                left: l0,
                right: r0,
            },
            Type::Product {
                left: l1,
                right: r1,
            },
        ) => {
            let gamma = subtype(&l0.fetch(state), &l1.fetch(state), state, context)?;

            subtype(&r0.fetch(state), &r1.fetch(state), state, gamma)
        }
        (Type::Variable { name: alpha }, Type::Variable { name: beta }) => {
            assert_eq!(alpha, beta);

            Ok(context)
        }
        (Type::Existential { id: alpha }, Type::Existential { id: beta }) if alpha == beta => {
            Ok(context)
        }
        (Type::Function { from: f0, to: t0 }, Type::Function { from: f1, to: t1 }) => {
            let theta = subtype(&f0.fetch(state), &f1.fetch(state), state, context)?;

            subtype(
                &t0.fetch(state).apply_context(state, theta),
                &t1.fetch(state).apply_context(state, theta),
                state,
                theta,
            )
        }
        (Type::Existential { id }, _) => {
            if !b.has_existential(id, state) {
                instantiate_left(id, b, state, context)
            } else {
                Err(Error::CircularSubtyping {
                    kind_a: Kind::from(*b),
                    kind_b: Kind::from(*a),
                    alpha: *id,
                })?
            }
        }
        (_, Type::Existential { id }) => {
            if !a.has_existential(id, state) {
                instantiate_right(a, id, state, context)
            } else {
                Err(Error::CircularSubtyping {
                    kind_a: Kind::from(*a),
                    kind_b: Kind::from(*b),
                    alpha: *id,
                })?
            }
        }
        (Type::Quantification { variable, codomain }, _) => {
            let alpha = state.fresh_existential();

            let gamma = context
                .push(context::Element::Marker { id: alpha })
                .push(context::Element::Existential { id: alpha });
            let codomain =
                codomain
                    .fetch(state)
                    .substitute(&alpha, &Type::Existential { id: alpha }, state);
            let delta = subtype(&codomain, b, state, context)?;

            delta.drain_until(context::Element::Marker { id: alpha }, state)
        }
        (_, Type::Quantification { variable, codomain }) => {
            let theta = context.push(context::Element::Variable { name: *variable });
            let delta = subtype(a, b, state, theta)?;

            delta.drain_until(context::Element::Variable { name: *variable }, state)
        }
        _ => Err(Error::InvalidSubtyping {
            kind_a: Kind::from(*a),
            kind_b: Kind::from(*b),
        })?,
    }
}

fn instantiate_left<'ctx>(
    alpha: &variable::Variable,
    b: &Type,
    state: &mut state::State,
    context: &'ctx mut context::Context,
) -> ::std::result::Result<&'ctx mut context::Context, crate::error::Error>
{
    let (mut left_context, right_context) =
        context.split_at(context::Element::Existential { id: *alpha }, state)?;

    if b.is_monotype(state) && b.is_well_formed(state, &mut left_context) {
        return context.insert_in_place(
            context::Element::Existential { id: *alpha },
            [context::Element::SolvedExistential {
                id: *alpha,
                ty: b.store(state),
            }],
            state,
        );
    }

    match b {
        &Type::Existential { id } => context.insert_in_place(
            context::Element::Existential { id },
            [context::Element::SolvedExistential {
                id,
                ty: Type::Existential { id: *alpha }.store(state),
            }],
            state,
        ),
        Type::Quantification { variable, codomain } => {
            let delta = instantiate_left(
                alpha,
                b,
                state,
                context.push(context::Element::Variable { name: *variable }),
            )?;

            delta.drain_until(context::Element::Variable { name: *variable }, state)
        }
        Type::Function { from, to } => {
            let beta1 = state.fresh_existential();
            let beta2 = state.fresh_existential();

            let gamma = context.insert_in_place(
                context::Element::Existential { id: *alpha },
                [
                    context::Element::Existential { id: beta2 },
                    context::Element::Existential { id: beta1 },
                    context::Element::SolvedExistential {
                        id: *alpha,
                        ty: Type::Function {
                            from: Type::Existential { id: beta1 }.store(state),
                            to: Type::Existential { id: beta2 }.store(state),
                        }
                        .store(state),
                    },
                ],
                state,
            )?;
            let theta = instantiate_right(&from.fetch(state), &beta1, state, gamma)?;
            let delta = instantiate_left(
                &beta2,
                &to.fetch(state).apply_context(state, theta),
                state,
                theta,
            )?;

            Ok(delta)
        }
        _ => todo!("Handle instantiating left an invalid type"),
    }
}

fn instantiate_right<'ctx>(
    a: &Type,
    beta: &variable::Variable,
    state: &mut state::State,
    context: &'ctx mut context::Context,
) -> ::std::result::Result<&'ctx mut context::Context, crate::error::Error>
{
    let (mut left_context, right_context) =
        context.split_at(context::Element::Existential { id: *beta }, state)?;

    if a.is_monotype(state) && a.is_well_formed(state, &mut left_context) {
        return context.insert_in_place(
            context::Element::Existential { id: *beta },
            [context::Element::SolvedExistential {
                id: *beta,
                ty: a.store(state),
            }],
            state,
        );
    }

    match a {
        Type::Product { left, right } => {
            let alpha1 = state.fresh_existential();
            let alpha2 = state.fresh_existential();

            let gamma = context.insert_in_place(
                context::Element::Existential { id: *beta },
                [
                    context::Element::Existential { id: alpha2 },
                    context::Element::Existential { id: alpha1 },
                    context::Element::SolvedExistential {
                        id: *beta,
                        ty: Type::Product {
                            left: Type::Existential { id: alpha1 }.store(state),
                            right: Type::Existential { id: alpha2 }.store(state),
                        }
                        .store(state),
                    },
                ],
                state,
            )?;
            let theta = instantiate_left(&alpha1, &left.fetch(state), state, gamma)?;
            let delta = instantiate_right(
                &right.fetch(state).apply_context(state, theta),
                &alpha2,
                state,
                theta,
            )?;

            Ok(delta)
        }
        &Type::Existential { id } => context.insert_in_place(
            context::Element::Existential { id },
            [context::Element::SolvedExistential {
                id,
                ty: Type::Existential { id: *beta }.store(state),
            }],
            state,
        ),
        Type::Quantification { variable, codomain } => {
            let alpha = state.fresh_existential();

            let gamma = context
                .push(context::Element::Marker { id: alpha })
                .push(context::Element::Existential { id: alpha });
            let delta = instantiate_right(
                &codomain.fetch(state).substitute(
                    variable,
                    &Type::Existential { id: alpha },
                    state,
                ),
                beta,
                state,
                gamma,
            )?;

            delta.drain_until(context::Element::Marker { id: alpha }, state)
        }
        Type::Function { from, to } => {
            let alpha1 = state.fresh_existential();
            let alpha2 = state.fresh_existential();

            let gamma = context.insert_in_place(
                context::Element::Existential { id: *beta },
                [
                    context::Element::Existential { id: alpha2 },
                    context::Element::Existential { id: alpha1 },
                    context::Element::SolvedExistential {
                        id: *beta,
                        ty: Type::Function {
                            from: Type::Existential { id: alpha1 }.store(state),
                            to: Type::Existential { id: alpha2 }.store(state),
                        }
                        .store(state),
                    },
                ],
                state,
            )?;
            let theta = instantiate_left(&alpha1, &from.fetch(state), state, gamma)?;
            let delta = instantiate_right(
                &to.fetch(state).apply_context(state, theta),
                &alpha2,
                state,
                theta,
            );

            delta
        }
        _ => todo!("Handle instantiating right an invalid type"),
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Kind
{
    Literal,
    Product,
    Variable,
    Existential,
    Quantification,
    Function,
}

impl From<Type> for Kind
{
    fn from(ty: Type) -> Self
    {
        match ty {
            Type::Literal { .. } => Kind::Literal,
            Type::Product { .. } => Kind::Product,
            Type::Variable { .. } => Kind::Variable,
            Type::Existential { .. } => Kind::Existential,
            Type::Quantification { .. } => Kind::Quantification,
            Type::Function { .. } => Kind::Function,
        }
    }
}

impl ::std::fmt::Display for Kind
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
    {
        match self {
            Kind::Literal => f.write_str("a literal"),
            Kind::Product => f.write_str("a product"),
            Kind::Variable => f.write_str("a variable"),
            Kind::Existential => f.write_str("an existential"),
            Kind::Quantification => f.write_str("a quantification"),
            Kind::Function => f.write_str("a function"),
        }
    }
}

#[allow(variant_size_differences)]
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Error
{
    InvalidApplication
    {
        kind: Kind
    },
    InvalidSubtyping
    {
        kind_a: Kind, kind_b: Kind
    },
    CircularSubtyping
    {
        kind_a: Kind,
        kind_b: Kind,
        alpha: variable::Variable,
    },
}

impl ::std::fmt::Display for Error
{
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result
    {
        match self {
            Error::InvalidApplication { kind } => {
                f.write_fmt(format_args!("cannot apply {kind} type"))
            }
            Error::InvalidSubtyping { kind_a, kind_b } => {
                f.write_fmt(format_args!("{kind_a} is not a subtype of {kind_b}"))
            }
            Error::CircularSubtyping { kind_a, kind_b,alpha} => f.write_fmt(format_args!(
                "cannot resolve subtyping relation from {kind_a} to {kind_b} as that would require instantiating {alpha} to {kind_b}"
            )),
        }
    }
}

impl ::std::error::Error for Error
{
    fn source(&self) -> Option<&(dyn ::std::error::Error + 'static)>
    {
        None
    }
}
