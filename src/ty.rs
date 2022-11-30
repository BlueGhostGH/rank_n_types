use crate::{context, intern, state};

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

    pub(crate) fn existential_occurs(&self, alpha: u64, state: &state::State) -> bool
    {
        match self {
            Type::Literal { .. } => false,
            Type::Product { left, right } => {
                let occurs_in_left = left.fetch(state).existential_occurs(alpha, state);
                let occurs_in_right = right.fetch(state).existential_occurs(alpha, state);

                occurs_in_left || occurs_in_right
            }
            Type::Existential { id } => &alpha == id,
            _ => unimplemented!("{:?}", self),
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
