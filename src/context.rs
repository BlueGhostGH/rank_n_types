use crate::{intern, state, ty};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum Element
{
    Variable
    {
        name: &'static str
    },
    TypedVariable
    {
        name: &'static str,
        ty: intern::Intern<ty::Type>,
    },
    Existential
    {
        id: u64
    },
    Solved
    {
        id: u64,
        ty: intern::Intern<ty::Type>,
    },
}

#[derive(Debug)]
pub(crate) struct Context
{
    elements: Vec<Element>,
}

impl Context
{
    pub(crate) fn initial() -> Self
    {
        Context {
            elements: Vec::new(),
        }
    }

    pub(crate) fn push(&mut self, element: Element) -> &mut Self
    {
        self.elements.push(element);

        self
    }

    pub(crate) fn insert_in_place<const N: usize>(
        &mut self,
        element: Element,
        inserts: [Element; N],
        state: &state::State,
    ) -> ::std::result::Result<&mut Self, crate::error::Error>
    {
        let index = self
            .elements
            .iter()
            .position(|elem| elem == &element)
            .ok_or(Error::ElementNotFound {
                element: element.with_kind(state),
            })?;

        let _count = self.elements.splice(index..=index, inserts).count();

        Ok(self)
    }

    pub(crate) fn drain_until(
        &mut self,
        element: Element,
        state: &state::State,
    ) -> ::std::result::Result<&mut Self, crate::error::Error>
    {
        let index = self
            .elements
            .iter()
            .position(|elem| elem == &element)
            .ok_or(Error::ElementNotFound {
                element: element.with_kind(state),
            })?;

        let _drained = self.elements.drain(index..);
        ::std::mem::drop(_drained);

        Ok(self)
    }

    pub(crate) fn split_at(
        &mut self,
        element: Element,
        state: &state::State,
    ) -> ::std::result::Result<(Self, Self), crate::error::Error>
    {
        let index = self
            .elements
            .iter()
            .position(|elem| elem == &element)
            .ok_or(Error::ElementNotFound {
                element: element.with_kind(state),
            })?;

        let (lhs, rhs) = self.elements.split_at(index);

        let left_context = {
            let elements = lhs.to_vec();
            Context { elements }
        };
        let right_context = {
            let elements = rhs.to_vec();
            Context { elements }
        };

        Ok((left_context, right_context))
    }

    pub(crate) fn has_variable(&self, alpha: &'static str) -> bool
    {
        self.elements
            .iter()
            .any(|elem| elem == &Element::Variable { name: alpha })
    }

    pub(crate) fn has_existential(&self, alpha: u64) -> bool
    {
        self.elements
            .iter()
            .any(|elem| elem == &Element::Existential { id: alpha })
    }

    pub(crate) fn fetch_annotation(
        &self,
        variable_name: &str,
        state: &state::State,
    ) -> Option<ty::Type>
    {
        self.elements
            .iter()
            .filter_map(|elem| {
                if let Element::TypedVariable { name, ty } = elem {
                    Some((name, ty))
                } else {
                    None
                }
            })
            .find(|(name, _)| name == &&variable_name)
            .map(|(_, ty)| ty.fetch(state))
    }

    pub(crate) fn fetch_solved(&self, alpha: u64, state: &state::State) -> Option<ty::Type>
    {
        self.elements
            .iter()
            .filter_map(|elem| {
                if let Element::Solved { id, ty } = elem {
                    Some((id, ty))
                } else {
                    None
                }
            })
            .find(|(id, _)| id == &&alpha)
            .map(|(_, ty)| ty.fetch(state))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(super) enum ElementWithKind
{
    Variable
    {
        name: &'static str
    },
    TypedVariable
    {
        name: &'static str, kind: ty::Kind
    },
    Existential
    {
        id: u64
    },
    Solved
    {
        id: u64, kind: ty::Kind
    },
}

impl ::std::fmt::Display for ElementWithKind
{
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result
    {
        match self {
            ElementWithKind::Variable { name } => f.write_fmt(format_args!("variable {name}")),
            ElementWithKind::TypedVariable { name, kind } => {
                f.write_fmt(format_args!("variable {name} of type {kind}"))
            }
            ElementWithKind::Existential { id } => f.write_fmt(format_args!("existential t{id}")),
            ElementWithKind::Solved { id, kind } => {
                f.write_fmt(format_args!("existential t{id} solved with type {kind}"))
            }
        }
    }
}

impl Element
{
    fn with_kind(&self, state: &state::State) -> ElementWithKind
    {
        match self {
            Element::Variable { name } => ElementWithKind::Variable { name },
            Element::TypedVariable { name, ty } => ElementWithKind::TypedVariable {
                name,
                kind: ty::Kind::from(ty.fetch(state)),
            },
            &Element::Existential { id } => ElementWithKind::Existential { id },
            &Element::Solved { id, ty } => ElementWithKind::Solved {
                id,
                kind: ty::Kind::from(ty.fetch(state)),
            },
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Error
{
    ElementNotFound
    {
        element: ElementWithKind
    },
}

impl ::std::fmt::Display for Error
{
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result
    {
        match self {
            Error::ElementNotFound { element } => {
                f.write_fmt(format_args!("could not find the {element} in context"))
            }
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
