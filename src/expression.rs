use crate::{context, state, ty};

#[derive(Debug)]
pub(crate) enum Literal
{
    Bool(bool),
    String(&'static str),
}

impl Literal
{
    fn synthesize(&self) -> ty::Literal
    {
        match self {
            Literal::Bool(_) => ty::Literal::Bool,
            Literal::String(_) => ty::Literal::String,
        }
    }
}

#[derive(Debug)]
pub(crate) enum Expression
{
    Literal
    {
        literal: Literal
    },
    Tuple
    {
        first: Box<Expression>,
        second: Box<Expression>,
    },
    Let
    {
        name: &'static str,
        expr: Box<Expression>,
        body: Box<Expression>,
    },
    Variable
    {
        name: &'static str
    },
    Annotation
    {
        expr: Box<Expression>, ty: ty::Type
    },
    Abstraction
    {
        parameter: &'static str,
        body: Box<Expression>,
    },

    Application
    {
        function: Box<Expression>,
        argument: Box<Expression>,
    },
}

impl Expression
{
    pub(crate) fn synthesize<'ctx>(
        &self,
        state: &mut state::State,
        context: &'ctx mut context::Context,
    ) -> ::std::result::Result<(ty::Type, &'ctx mut context::Context), context::Error>
    {
        match self {
            Expression::Literal { literal } => Ok((
                ty::Type::Literal {
                    ty: literal.synthesize(),
                },
                context,
            )),
            Expression::Tuple { first, second } => {
                let (a, gamma) = first.synthesize(state, context)?;
                let (b, delta) = second.synthesize(state, gamma)?;

                Ok((
                    ty::Type::Product {
                        left: a.store(state),
                        right: b.store(state),
                    },
                    delta,
                ))
            }
            Expression::Let { name, expr, body } => {
                let (t0, gamma) = expr.synthesize(state, context)?;
                let theta = gamma.push(context::Element::TypedVariable {
                    name,
                    ty: t0.store(state),
                });

                let (t1, delta) = body.synthesize(state, theta)?;
                let omega = delta.insert_in_place(
                    context::Element::TypedVariable {
                        name,
                        ty: t0.store(state),
                    },
                    [],
                    state,
                )?;

                Ok((t1, omega))
            }
            Expression::Variable { name } => match context.fetch_annotation(name, state) {
                Some(annotation) => Ok((annotation, context)),
                None => unreachable!(),
            },
            Expression::Annotation { expr, ty } => {
                assert!(ty.is_well_formed(state, context));

                let delta = expr.checks_against(ty, state, context)?;

                Ok((*ty, delta))
            }
            Expression::Abstraction { parameter, body } => {
                let alpha = state.fresh_existential();
                let beta = state.fresh_existential();

                let gamma = context
                    .push(context::Element::Existential { id: alpha })
                    .push(context::Element::Existential { id: beta })
                    .push(context::Element::TypedVariable {
                        name: parameter,
                        ty: ty::Type::Existential { id: alpha }.store(state),
                    });

                let delta = body
                    .checks_against(&ty::Type::Existential { id: beta }, state, gamma)?
                    .drain_until(
                        context::Element::TypedVariable {
                            name: parameter,
                            ty: ty::Type::Existential { id: alpha }.store(state),
                        },
                        state,
                    )?;

                let ty = ty::Type::Function {
                    from: ty::Type::Existential { id: alpha }.store(state),
                    to: ty::Type::Existential { id: beta }.store(state),
                };

                Ok((ty, delta))
            }
            Expression::Application { function, argument } => {
                let (a, theta) = function.synthesize(state, context)?;

                argument.application_synthesize(&a.apply_context(state, theta), state, theta)
            }
        }
    }

    fn application_synthesize<'ctx>(
        &self,
        ty: &ty::Type,
        state: &mut state::State,
        context: &'ctx mut context::Context,
    ) -> ::std::result::Result<(ty::Type, &'ctx mut context::Context), context::Error>
    {
        match ty {
            ty::Type::Quantification { variable, codomain } => {
                let alpha = state.fresh_existential();
                let gamma = context.push(context::Element::Existential { id: alpha });
                let substituted_a = crate::substitute(
                    codomain.fetch(state),
                    variable,
                    ty::Type::Existential { id: alpha },
                    state,
                );

                self.application_synthesize(&substituted_a, state, gamma)
            }
            ty::Type::Function { from, to } => {
                let delta = self.checks_against(&from.fetch(state), state, context)?;

                Ok((to.fetch(state), delta))
            }
            _ => unimplemented!("{:?}", ty),
        }
    }

    fn checks_against<'ctx>(
        &self,
        ty: &ty::Type,
        state: &mut state::State,
        context: &'ctx mut context::Context,
    ) -> ::std::result::Result<&'ctx mut context::Context, context::Error>
    {
        assert!(ty.is_well_formed(state, context));
        match (self, &ty) {
            (Expression::Literal { literal }, ty::Type::Literal { ty }) => unimplemented!(),
            (Expression::Abstraction { parameter, body }, ty::Type::Function { from, to }) => {
                let typed_variable = context::Element::TypedVariable {
                    name: parameter,
                    ty: *from,
                };
                let gamma = context.push(typed_variable);

                Ok(body
                    .checks_against(&to.fetch(state), state, gamma)?
                    .drain_until(typed_variable, state)?)
            }
            (Expression::Tuple { first, second }, ty::Type::Product { left, right }) => {
                unimplemented!()
            }
            (_, ty::Type::Quantification { variable, codomain }) => {
                let variable = context::Element::Variable { name: variable };
                let gamma = context.push(variable);

                Ok(self
                    .checks_against(&codomain.fetch(state), state, context)?
                    .drain_until(variable, state)?)
            }
            (_, _) => {
                let (a, theta) = self.synthesize(state, context)?;

                let a = a.apply_context(state, theta);
                let b = ty.apply_context(state, theta);
                crate::subtype(&a, &b, state, theta)
            }
        }
    }
}
