use crate::no_std::{pipelines::{tap::Tap, pipe::Pipe}, functions::ext::FnOnceExt};
use std::{prelude::v1::*, fmt::{Debug, Display}, time::Duration, sync::{Arc, Mutex, RwLock}};
use minstant::Instant;

/// This trait is to implement some extension functions,
/// which need a generic return type, for any sized type.
pub trait StdAnyExt1<R>: Sized {
    /// Executes the given closure block and returns the duration of elapsed time interval.
    fn ext_measure_time(self, f: impl FnOnce(Self) -> R) -> Duration {
        Instant::now().tap(|_| f(self)).elapsed()
    }

    /// Executes the given closure block,
    /// returns the duration of elapsed time interval and the result of the closure execution.
    fn ext_measure_time_with_value(self, f: impl FnOnce(Self) -> R) -> (Duration, R) {
        Instant::now()
            .pipe(|t| (f(self), t.elapsed()))
            .pipe(|(v, e)| (e, v))
    }

    /// Executes the given closure block,
    /// returns the duration of elapsed time interval and the receiver `self`.
    fn ext_measure_time_with_self(self, f: impl FnOnce(&Self) -> R) -> (Duration, Self) {
        Instant::now().tap(|_| f(&self)).pipe(|t| (t.elapsed(), self))
    }

    /// Executes the given closure block,
    /// returns the duration of elapsed time interval and the receiver `self`.
    fn ext_measure_time_with_mut_self(mut self, f: impl FnOnce(&mut Self) -> R) -> (Duration, Self) {
        Instant::now().tap(|_| f(&mut self)).pipe(|t| (t.elapsed(), self))
    }
}

impl<T, R> StdAnyExt1<R> for T {}

/// This trait is to implement some extension functions for any sized type.
pub trait StdAnyExt: Sized {
    /// System output -> with `:#?`'s `println!`.
    ///
    /// Consumes `self`, `println!` with `:#?`, returns `self`.
    fn dbg(self) -> Self where Self: Debug {
        self.tap(|s| println!("{s:#?}"))
    }

    /// System output -> with `:?`'s `println!`.
    ///
    /// Consumes `self`, `println!` with `:?`, returns `self`.
    fn sout(self) -> Self where Self: Debug {
        self.tap(|s| println!("{s:?}"))
    }

    /// Consumes `self`, `println!` as it is, returns `self`.
    fn echo(self) -> Self where Self: Display {
        self.tap(|s| println!("{s}"))
    }

    /// Convert `value` to `Mutex::new(value)`
    fn into_mutex(self) -> Mutex<Self> {
        self.pipe(Mutex::new)
    }

    /// Convert `value` to `Arc::new(Mutex::new(value))`
    fn into_arc_mutex(self) -> Arc<Mutex<Self>> {
        Arc::new.compose(Mutex::new)(self)
    }

    /// Convert `value` to `RwLock::new(value)`
    fn into_rwlock(self) -> RwLock<Self> {
        self.pipe(RwLock::new)
    }

    /// Convert `value` to `Arc::new(RwLock::new(value))`
    fn into_arc_rwlock(self) -> Arc<RwLock<Self>> {
        Arc::new.compose(RwLock::new)(self)
    }
}

impl<T> StdAnyExt for T {}