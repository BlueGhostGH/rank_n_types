#[derive(Debug, Clone, Copy, Eq)]
pub(crate) enum Variable
{
    Named
    {
        name: &'static str
    },
    Existential
    {
        id: u64
    },
}

fn id_from_name(
    name: &str,
) -> ::std::option::Option<::std::result::Result<u64, ::std::num::ParseIntError>>
{
    // An existential name is of the shape ?{n},
    // where {n} is a whole, but existentials  are u64's,
    // therefore the first char must be discarded
    let id = name.get(1..)?;

    Some(id.parse())
}

impl PartialEq for Variable
{
    fn eq(&self, other: &Self) -> bool
    {
        match (self, other) {
            (Variable::Named { name: alpha }, Variable::Named { name: beta }) => alpha == beta,
            (Variable::Existential { id: alpha }, Variable::Existential { id: beta }) => {
                alpha == beta
            }
            (Variable::Named { name }, &Variable::Existential { id }) => {
                matches!(id_from_name(name),
                Some(Ok(alpha)) if alpha == id)
            }
            (existential, named) => named == existential,
        }
    }
}

impl ::std::fmt::Display for Variable
{
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result
    {
        match self {
            Variable::Named { name } => f.write_str(name),
            Variable::Existential { id } => f.write_fmt(format_args!("?{id}")),
        }
    }
}
