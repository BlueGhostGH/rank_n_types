use crate::context;

#[derive(Debug)]
pub(crate) enum Error
{
    Context
    {
        error: context::Error
    },
}

impl ::std::fmt::Display for Error
{
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result
    {
        match self {
            Error::Context { error } => f.write_fmt(format_args!("{error}")),
        }
    }
}

impl ::std::error::Error for Error
{
    fn source(&self) -> Option<&(dyn ::std::error::Error + 'static)>
    {
        match self {
            Error::Context { error } => Some(error),
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
