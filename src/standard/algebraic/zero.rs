use crate::no_std::algebraic::zero::ParseUnitError;
use std::error;

impl error::Error for ParseUnitError {}