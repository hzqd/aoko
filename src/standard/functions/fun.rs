use crate::no_std::{functions::ext::AnyExt1, algebraic::sum::TimeUnit};
use std::{prelude::v1::*, io::stdin, time::{Instant, Duration}};

/// Reads a line of input from the standard input stream.
///
/// Returns a `Some` value when content is not empty.
///
/// # Examples
///
/// ```no_run
/// use aoko::standard::functions::fun::*;
/// 
/// // If you ensure the input is not empty, or want to panic if it is empty, use:
/// read_line().unwrap();
///
/// // If you want to return a default value when the input is empty, use:
/// read_line().unwrap_or(String::from("default_value"));
///
/// // If you just want empty value is "", use:
/// read_line().unwrap_or_default();
/// ```
pub fn read_line() -> Option<String> {
    String::new().also_mut(|s| stdin().read_line(s))
        .trim_end().to_string()
        .let_owned(|s| if s.len() > 0 { Some(s) } else { None })
}

/// Breaks loop when command line input is empty. (Press `Enter` to exit.)
///
/// Usually used in command line program as `.exe` file on Windows to prevent it from exiting directly.
pub fn wait_enter() {
    while read_line() != None {}
}

/// Executes the given closure block and returns the duration of elapsed time interval.
pub fn measure_time<R>(f: impl FnOnce() -> R) -> Duration {
    Instant::now().also_ref(|_| f()).elapsed()
}

/// Executes the given closure block,
/// returns the result of the closure execution and the duration of elapsed time interval.
pub fn measure_time_with_value<R>(f: impl FnOnce() -> R) -> (R, Duration) {
    Instant::now().let_owned(|s| (f(), s.elapsed()))
}

/// Takes `TimeUnit` as a parameter,
/// returns conversion function.
pub fn time_conversion(u: &TimeUnit) -> impl FnOnce(Duration) -> u128 {
    use TimeUnit::*;
    match u {
        Nanos => |elapsed: Duration| elapsed.as_nanos(),
        Micros => |elapsed: Duration| elapsed.as_micros(),
        Millis => |elapsed: Duration| elapsed.as_millis(),
        Secs => |elapsed: Duration| elapsed.as_secs() as u128,
    }
}

/// Takes `TimeUnit` as a parameter,
/// returns conversion function and the unit.
pub fn time_conversion_with_unit(u: TimeUnit) -> (impl FnOnce(Duration) -> u128, TimeUnit) {
    time_conversion(&u).let_owned(|f| (f, u))
}
