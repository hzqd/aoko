use crate::no_std::{algebraic::zero::ParseUnitError, functions::ext::AnyExt};
use core::str::FromStr;

#[derive(Debug)]
pub enum TimeUnit {
    Nanos,
    Micros,
    Millis,
    Secs,
}

impl FromStr for TimeUnit {
    type Err = ParseUnitError;

    fn from_str(unit: &str) -> Result<TimeUnit, ParseUnitError> {
        use TimeUnit::*;
        match unit {
            "nanos" => Nanos.into_ok(),
            "micros" => Micros.into_ok(),
            "millis" => Millis.into_ok(),
            "secs" => Secs.into_ok(),
            _ => ParseUnitError.into_err()
        }
    }
}