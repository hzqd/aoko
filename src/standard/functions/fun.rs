use crate::no_std::{algebraic::sum::TimeUnit, pipelines::{pipe::Pipe, tap::Tap}};
use std::{prelude::v1::*, io::stdin, time::Duration};
use minstant::Instant;

/// Reads a line of input from the standard input stream.
///
/// # Panics
/// 
/// Panics when the input is not UTF-8.
pub fn read_line() -> String {
    String::new().tap_mut(|s| stdin().read_line(s).expect("Invalid UTF-8"))
}

/// Breaks loop when command line input is empty. (Press `Enter` to exit/confirm.)
///
/// Usually used in command line program as `.exe` file on Windows to prevent it from exiting directly.
pub fn wait_enter() {
    while read_line().trim_end().bytes().next().is_some() {}
}

/// Executes the given closure block and returns the duration of elapsed time interval.
pub fn measure_time<R>(f: impl FnOnce() -> R) -> Duration {
    Instant::now().tap(|_| f()).elapsed()
}

/// Executes the given closure block,
/// returns the duration of elapsed time interval and the result of the closure execution.
pub fn measure_time_with_value<R>(f: impl FnOnce() -> R) -> (Duration, R) {
    Instant::now()
        .pipe(|t| (f(), t.elapsed()))
        .pipe(|(v, e)| (e, v))
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
    time_conversion(&u).pipe(|f| (f, u))
}
