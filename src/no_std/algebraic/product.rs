use core::fmt;
use std::error::Error;

#[derive(Debug)]
pub struct StrErr<'a>(pub &'a str);
impl Error for StrErr<'_> {}
impl fmt::Display for StrErr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}