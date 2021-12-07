use crate::no_std::functions::ext::AnyExt1;
use std::{prelude::v1::*, fmt::{Debug, Display}, time::{Instant, Duration}};

/// This trait is to implement some extension functions,
/// which need a generic return type, for any sized type.
pub trait StdAnyExt1<R>: Sized {
    /// Executes the given closure block and returns the duration of elapsed time interval.
    fn measure_time(self, f: impl FnOnce(Self) -> R) -> Duration {
        Instant::now().also_ref(|_| f(self)).elapsed()
    }

    /// Executes the given closure block,
    /// returns the result of the closure execution and the duration of elapsed time interval.
    fn measure_time_with_value(self, f: impl FnOnce(Self) -> R) -> (R, Duration) {
        Instant::now().let_owned(|s| (f(self), s.elapsed()))
    }

    /// Executes the given closure block,
    /// returns the receiver `self` and the duration of elapsed time interval.
    fn measure_time_with_self(self, f: impl FnOnce(&Self) -> R) -> (Self, Duration) {
        Instant::now().also_ref(|_| f(&self)).let_owned(|s| (self, s.elapsed()))
    }

    /// Executes the given closure block,
    /// returns the receiver `self` and the duration of elapsed time interval.
    fn measure_time_with_mut_self(mut self, f: impl FnOnce(&mut Self) -> R) -> (Self, Duration) {
        Instant::now().also_ref(|_| f(&mut self)).let_owned(|s| (self, s.elapsed()))
    }
}

impl<T, R> StdAnyExt1<R> for T {}

/// This trait is to implement some extension functions for any sized type.
pub trait StdAnyExt: Sized {
    /// System output -> with `:#?`'s `println!`.
    ///
    /// Consumes `self`, `println!` with `:#?`, returns `self`.
    fn dbg(self) -> Self where Self: Debug {
        self.also_ref(|s| println!("{:#?}", s))
    }

    /// System output -> with `:?`'s `println!`.
    ///
    /// Consumes `self`, `println!` with `:?`, returns `self`.
    fn sout(self) -> Self where Self: Debug {
        self.also_ref(|s| println!("{:?}", s))
    }

    /// Consumes `self`, `println!` as it is, returns `self`.
    fn echo(self) -> Self where Self: Display {
        self.also_ref(|s| println!("{}", s))
    }
}

impl<T> StdAnyExt for T {}