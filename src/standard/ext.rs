use crate::no_std::ext::AnyExt1;
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
    fn sout(self) -> Self where Self: Debug {
        self.also_ref(|s| println!("{:#?}", s))
    }

    /// Consumes `self`, `println!` as it is, returns `self`.
    fn echo(self) -> Self where Self: Display {
        self.also_ref(|s| println!("{}", s))
    }

    /// Returns the name of a type as a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::standard::ext::*;
    ///
    /// assert_eq!("".type_name(), "&str");     // auto ref, auto deref.
    /// assert_eq!((&"").type_name(), "&str");  // auto deref.
    /// assert_eq!((&&"").type_name(), "&&str");
    /// ```
    fn type_name(&self) -> &str {
        std::any::type_name::<Self>()
    }
    
    /// Returns the size of a type in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::standard::ext::*;
    ///
    /// assert_eq!(().type_size(), 0);      // auto ref, auto deref.
    /// assert_eq!((&()).type_size(), 0);   // auto deref.
    /// assert_eq!((&&()).type_size(), 8);
    /// ```
    fn type_size(&self) -> usize {
        std::mem::size_of::<Self>()
    }
}

impl<T> StdAnyExt for T {}

/// This trait is to implement some extension functions for `u128` type.
pub trait StdU128Ext {
    fn fmt_size_from(self, unit: char) -> String;
}

impl StdU128Ext for u128 {
    /// Human readable storage unit.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::standard::ext::*;
    ///
    /// assert_eq!(String::from("32.0 G"), 33554432.fmt_size_from('K'));
    /// ```
    fn fmt_size_from(self, unit: char) -> String {
        let units = ['B', 'K', 'M', 'G', 'T', 'P', 'E', 'Z'];
        let mut size = self as f64;
        let mut counter = 0;
        
        while size >= 1024.0 {
            size /= 1024.0;
            counter += 1;
        }
    
        for (i, &c) in units.iter().enumerate() { 
            if c == unit {
                counter += i;
                break;
            }
        }
    
        format!("{:.1} {}", size, units.get(counter).unwrap_or_else(|| panic!("memory unit out of bounds")))
    }
}

/// This trait is to implement some extension functions whose type is `FnOnce`.
pub trait StdFnOnceExt<P1, P2, R> {
    fn partial2(self, p2: P2) -> Box<dyn FnOnce(P1) -> R>;
}

impl<P1, P2: 'static, R, F> StdFnOnceExt<P1, P2, R> for F where F: FnOnce(P1, P2) -> R + 'static {
    /// Two parameters, currying from right to left.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::standard::ext::*;
    ///
    /// fn foo(a: u8, b: u8) -> u8 { a - b }
    /// assert_eq!(foo.partial2(2)(3), 1);
    /// ```
    fn partial2(self, p2: P2) -> Box<dyn FnOnce(P1) -> R> {
        Box::new(move |p1| self(p1, p2))
    }
}
