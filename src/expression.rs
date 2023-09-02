use crate::{context, state, ty, variable};

#[derive(Debug)]
pub(crate) enum Literal
{
    Unit,
    Boolean,
    Number,
    String,
}

impl Literal
{
    fn synthesize(&self) -> ty::Literal
    {
        match self {
            Literal::Unit => ty::Literal::Unit,
            Literal::Boolean => ty::Literal::Boolean,
            Literal::Number => ty::Literal::Number,
            Literal::String => ty::Literal::String,
        }
    }

    fn checks_against_ty(&self, ty: &ty::Literal) -> bool
    {
        &self.synthesize() == ty
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
    ) -> ::std::result::Result<(ty::Type, &'ctx mut context::Context), crate::error::Error>
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
                    name: variable::Variable::Named { name },
                    ty: t0.store(state),
                });

                let (t1, delta) = body.synthesize(state, theta)?;
                let omega = delta.insert_in_place(
                    context::Element::TypedVariable {
                        name: variable::Variable::Named { name },
                        ty: t0.store(state),
                    },
                    [],
                    state,
                )?;

                Ok((t1, omega))
            }
            Expression::Variable { name } => {
                match context.fetch_annotation(&variable::Variable::Named { name }, state) {
                    Some(annotation) => Ok((annotation, context)),
                    None => unreachable!(),
                }
            }
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
                        name: variable::Variable::Named { name: parameter },
                        ty: ty::Type::Existential { id: alpha }.store(state),
                    });

                let delta = body
                    .checks_against(&ty::Type::Existential { id: beta }, state, gamma)?
                    .drain_until(
                        context::Element::TypedVariable {
                            name: variable::Variable::Named { name: parameter },
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

                Ok(a.apply_context(state, theta)
                    .synthesize_application(argument, state, theta)?)
            }
        }
    }

    pub(crate) fn checks_against<'ctx>(
        &self,
        ty: &ty::Type,
        state: &mut state::State,
        context: &'ctx mut context::Context,
    ) -> ::std::result::Result<&'ctx mut context::Context, crate::error::Error>
    {
        assert!(ty.is_well_formed(state, context));
        match (self, ty) {
            (Expression::Literal { literal }, ty::Type::Literal { ty }) => {
                assert!(literal.checks_against_ty(ty));

                Ok(context)
            }
            (Expression::Abstraction { parameter, body }, ty::Type::Function { from, to }) => {
                let typed_variable = context::Element::TypedVariable {
                    name: variable::Variable::Named { name: parameter },
                    ty: *from,
                };
                let gamma = context.push(typed_variable);

                Ok(body
                    .checks_against(&to.fetch(state), state, gamma)?
                    .drain_until(typed_variable, state)?)
            }
            (Expression::Tuple { first, second }, ty::Type::Product { left, right }) => {
                let gamma = first.checks_against(&left.fetch(state), state, context)?;

                second.checks_against(&right.fetch(state), state, gamma)
            }
            (_, ty::Type::Quantification { variable, codomain }) => {
                let variable = context::Element::Variable { name: *variable };
                let gamma = context.push(variable);

                Ok(self
                    .checks_against(&codomain.fetch(state), state, context)?
                    .drain_until(variable, state)?)
            }
            (_, _) => {
                let (a, theta) = self.synthesize(state, context)?;

                let a = a.apply_context(state, theta);
                let b = ty.apply_context(state, theta);

                Ok(ty::subtype(&a, &b, state, theta)?)
            }
        }
    }
}
