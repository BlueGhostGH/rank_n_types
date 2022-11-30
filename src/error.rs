use crate::{context, ty};

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Error
{
    Context
    {
        error: context::Error
    },
    Ty
    {
        error: ty::Error
    },
}

impl ::std::fmt::Display for Error
{
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result
    {
        match self {
            Error::Context { error } => f.write_fmt(format_args!("{error}")),
            Error::Ty { error } => f.write_fmt(format_args!("{error}")),
        }
    }
}

impl ::std::error::Error for Error
{
    fn source(&self) -> Option<&(dyn ::std::error::Error + 'static)>
    {
        match self {
            Error::Context { error } => Some(error),
            Error::Ty { error } => Some(error),
        }
    }
}

impl From<context::Error> for Error
{
    fn from(error: context::Error) -> Self
    {
        Error::Context { error }
    }
}

impl From<ty::Error> for Error
{
    fn from(error: ty::Error) -> Self
    {
        Error::Ty { error }
    }
}
