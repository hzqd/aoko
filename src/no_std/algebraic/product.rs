use core::fmt::{self, Debug};
use std::error::Error;

#[derive(Debug)]
pub struct GErr<T>(pub T);
impl<T: Debug> Error for GErr<T> {}
impl<T: Debug> fmt::Display for GErr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}