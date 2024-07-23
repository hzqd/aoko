use core::fmt::Debug;
use std::error::Error;

use crate::no_std::algebraic::product::GErr;

impl<T: Debug> Error for GErr<T> {}