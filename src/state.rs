use crate::{
    intern::{self, Interner},
    ty, variable,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct State
{
    existentials_count: u64,
    pub(crate) types: Vec<ty::Type>,
}

impl State
{
    pub(crate) fn initial() -> Self
    {
        State {
            existentials_count: 0,
            types: Vec::new(),
        }
    }

    pub(crate) fn fresh_existential(&mut self) -> variable::Variable
    {
        let id = self.existentials_count;
        self.existentials_count += 1;

        variable::Variable::Existential { id }
    }
}

impl Interner<ty::Type> for State
{
    fn fetch(&self, intern::Intern { index, .. }: intern::Intern<ty::Type>) -> ty::Type
    {
        self.types[index]
    }

    fn store(&mut self, value: ty::Type) -> intern::Intern<ty::Type>
    {
        let index = self.types.len();
        self.types.push(value);

        intern::Intern {
            index,
            phantom: ::std::marker::PhantomData,
        }
    }
}
