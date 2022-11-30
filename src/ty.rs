use crate::{context, expression, intern, state};

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
        name: &'static str
    },
    Existential
    {
        id: u64
    },
    Quantification
    {
        variable: &'static str,
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
    ) -> ::std::result::Result<(Type, &'ctx mut context::Context), expression::Error>
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
                        context::Element::Solved {
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
                let substituted_a = crate::substitute(
                    codomain.fetch(state),
                    variable,
                    Type::Existential { id: alpha },
                    state,
                );

                substituted_a.synthesize_application(expr, state, gamma)
            }
            Type::Function { from, to } => {
                let delta = expr.checks_against(&from.fetch(state), state, context)?;

                Ok((to.fetch(state), delta))
            }
            _ => todo!("Handle applying wrong type"),
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
                if let Some(tau) = context.fetch_solved(id, state) {
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
                context.has_existential(*id) || context.fetch_solved(*id, state).is_some()
            }
            Type::Quantification {
                variable: variable_name,
                codomain,
            } => codomain.fetch(state).is_well_formed(
                state,
                context.push(context::Element::Variable {
                    name: variable_name,
                }),
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

    pub(crate) fn has_existential(&self, alpha: u64, state: &state::State) -> bool
    {
        match self {
            Type::Literal { .. } => false,
            Type::Product { left, right } => {
                let occurs_in_left = left.fetch(state).has_existential(alpha, state);
                let occurs_in_right = right.fetch(state).has_existential(alpha, state);

                occurs_in_left || occurs_in_right
            }
            Type::Variable { name } => {
                // An existential name is of the shape t{n},
                // where {n} is a whole, but existentials  are u64's,
                // therefore the first char must be discarded
                let n = &name[1..];

                match n.parse() {
                    Ok(beta) => alpha == beta,
                    Err(_) => false,
                }
            }
            Type::Existential { id } => &alpha == id,
            Type::Quantification { variable, codomain } => {
                // Same logic as for `Variable`
                let n = &variable[1..];

                match n.parse() {
                    Ok(beta) => alpha == beta,
                    Err(_) => codomain.fetch(state).has_existential(alpha, state),
                }
            }
            Type::Function { from, to } => {
                let occurs_in_from = from.fetch(state).has_existential(alpha, state);
                let occurs_in_to = to.fetch(state).has_existential(alpha, state);

                occurs_in_from || occurs_in_to
            }
        }
    }
}

#[derive(Debug)]
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
            Kind::Literal => f.write_str("literal"),
            Kind::Product => f.write_str("product"),
            Kind::Variable => f.write_str("variable"),
            Kind::Existential => f.write_str("existential"),
            Kind::Quantification => f.write_str("quantification"),
            Kind::Function => f.write_str("function"),
        }
    }
}
