use crate::no_std::{algebraic::zero::ParseUnitError, functions::ext::AnyExt};
use core::str::FromStr;

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
            "nanos" => Nanos.as_ok(),
            "micros" => Micros.as_ok(),
            "millis" => Millis.as_ok(),
            "secs" => Secs.as_ok(),
            _ => ParseUnitError.as_err()
        }
    }
}