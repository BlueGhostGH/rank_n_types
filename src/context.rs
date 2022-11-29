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
    ) -> &mut Self
    {
        match self.elements.iter().position(|elem| elem == &element) {
            Some(index) => {
                let _count = self.elements.splice(index..=index, inserts).count();
            }
            None => unreachable!("{:?}", (&self.elements, element)),
        };

        self
    }

    pub(crate) fn drain_until(&mut self, element: Element) -> &mut Self
    {
        match self.elements.iter().position(|elem| elem == &element) {
            Some(index) => {
                let _drained = self.elements.drain(index..);
            }
            None => unreachable!(),
        };

        self
    }

    pub(crate) fn split_at(&mut self, element: Element) -> (Self, Self)
    {
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
