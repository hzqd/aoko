use core::fmt;

pub struct ParseUnitError;

impl fmt::Display for ParseUnitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        "Unsupported unit".fmt(f)
    }
}