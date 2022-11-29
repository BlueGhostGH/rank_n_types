#[derive(Debug, Eq, Clone, Copy)]
pub(crate) struct Intern<T>
{
    pub(crate) index: usize,
    pub(crate) phantom: ::std::marker::PhantomData<T>,
}

pub(crate) trait Interner<T>
where
    T: Copy,
{
    fn fetch(&self, intern: Intern<T>) -> T;
    fn store(&mut self, value: T) -> Intern<T>;
}

impl<T> Intern<T>
where
    T: Copy,
{
    pub(crate) fn fetch<S>(&self, state: &S) -> T
    where
        S: Interner<T>,
    {
        state.fetch(*self)
    }
}

impl<T> PartialEq for Intern<T>
{
    fn eq(&self, _other: &Self) -> bool
    {
        // NOTE: We don't care about the index, just the value it points to
        true
    }
}
