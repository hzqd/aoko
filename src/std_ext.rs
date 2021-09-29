use cora::ext::AnyExt1;
use std::{fmt::{Debug, Display}, iter::Product, ops::Add};
use rayon::{iter::Either, prelude::*};
use std::time::{Instant, Duration};

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
    /// use aoko::std_ext::*;
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
    /// use aoko::std_ext::*;
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
    /// use aoko::std_ext::*;
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
    /// use aoko::std_ext::*;
    ///
    /// fn foo(a: u8, b: u8) -> u8 { a - b }
    /// assert_eq!(foo.partial2(2)(3), 1);
    /// ```
    fn partial2(self, p2: P2) -> Box<dyn FnOnce(P1) -> R> {
        Box::new(move |p1| self(p1, p2))
    }
}

pub trait StdSort<T> {
    fn sort(self) -> Vec<T>;
}

impl<T: Ord + Send> StdSort<T> for Vec<T> {
    /// Sorts `Vec` in parallel.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// vec![7, 4, 9, 2].sort().sout();
    /// ```
    fn sort(self) -> Vec<T> {
        self.also_mut(|v| v.par_sort())
    }
}

/// This trait is to implement some extension functions for `Vec` type,
/// which need two generic types and reference.
pub trait StdVecExt2<'a, T, R> where T: 'a {
    fn map(&'a self, f: impl Fn(&'a T) -> R + Sync + Send) -> Vec<R>;
    fn filter_map(&'a self, f: impl Fn(&'a T) -> Option<R> + Sync + Send) -> Vec<R>;
}

impl<'a, T, R> StdVecExt2<'a, T, R> for Vec<T> where T: 'a + Sync, R: Send {
    /// Returns a `Vec` containing the results of applying the given `f` function 
    /// to each element in the original `Vec`.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// assert_eq!(vec![1, 2, 3].map(|i| i + 1), vec![2, 3, 4]);
    /// ```
    fn map(&'a self, f: impl Fn(&'a T) -> R + Sync + Send) -> Vec<R> {
        self.par_iter().map(f).collect()
    }

    /// A combined map and filter. Filtering is handled via `Option` instead of `Boolean`
    /// such that the output type `R` can be different than the input type `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// let v = vec!["apple", "1", "banana", "2"]
    ///     .filter_map(|s| s.parse::<u8>().ok());
    /// assert_eq!(v, vec![1, 2]);
    /// ```
    fn filter_map(&'a self, f: impl Fn(&'a T) -> Option<R> + Sync + Send) -> Vec<R> {
        self.par_iter().filter_map(f).collect()
    }
}

/// This trait is to implement some extension functions for `Vec` type,
/// which need one generic type, and do not need reference.
pub trait StdVecExt1<T> {
    fn for_each<R>(self, f: impl Fn(T) -> R + Sync + Send);
    fn on_each<R>(self, f: impl Fn(&mut T) -> R + Sync + Send) -> Self;
    fn filter(self, f: impl Fn(&T) -> bool + Sync + Send) -> Vec<T>;
    fn fold(self, init: T, f: impl Fn(T, T) -> T + Sync + Send) -> T where T: Sync + Copy;
    fn reduce(self, f: impl Fn(T, T) -> T + Sync + Send) -> T where T: Sync + Copy + Default;
    fn sum(self) -> T where T: Sync + Copy + Default + Add<Output = T>;
    fn product(self) -> T where T: Product;
    fn partition(self, f: impl Fn(&T) -> bool + Sync + Send) -> (Vec<T>, Vec<T>);
    fn partition3(self, predicate1: impl Fn(&T) -> bool + Sync + Send, predicate2: impl Fn(&T) -> bool + Sync + Send) -> (Vec<T>, Vec<T>, Vec<T>) where T: Sync;
}

impl<T> StdVecExt1<T> for Vec<T> where T: Send {
    /// Executes `f` on each item produced by the iterator for `Vec` in parallel.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// vec![String::from("abc"), String::from("xyz")]
    ///     .for_each(|e| e.echo());
    /// ```
    fn for_each<R>(self, f: impl Fn(T) -> R + Sync + Send) {
        self.into_par_iter().for_each(|e| { f(e); });
    }

    /// Performs the given `f` on each element in parallel, and returns the `Vec` itself afterwards.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// assert_eq!(vec!["hello", "rust"].on_each(|s| *s.echo()), vec!["hello", "rust"]);
    /// ```
    fn on_each<R>(self, f: impl Fn(&mut T) -> R + Sync + Send) -> Self {
        self.also_mut(|v| v.par_iter_mut().for_each(|e| { f(e); }))
    }

    /// Returns a `Vec` containing only elements matching the given `f` predicate in parallel.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// assert_eq!(vec![1, 2, 3, 4].filter(|i| i % 2 == 0), vec![2, 4]);
    /// ```
    fn filter(self, f: impl Fn(&T) -> bool + Sync + Send) -> Vec<T> {
        self.into_par_iter().filter(f).collect()
    }

    /// Accumulates value starting with initial value,
    /// and applying operation `f` from left to right in parallel.
    ///
    /// Returns the specified initial value if the `Vec` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// assert_eq!(vec![1, 2, 3, 4].fold(0, |acc, i| acc + i), 10);
    /// ```
    fn fold(self, init: T, f: impl Fn(T, T) -> T + Sync + Send) -> T where T: Sync + Copy {
        self.into_par_iter().reduce(|| init, f)
    }

    /// Accumulates value starting with default value,
    /// and applying operation `f` from left to right in parallel.
    ///
    /// Returns the default value if the `Vec` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// assert_eq!(vec![1, 2, 3, 4].reduce(|acc, i| acc + i), 10);
    /// ```
    fn reduce(self, f: impl Fn(T, T) -> T + Sync + Send) -> T where T: Sync + Copy + Default {
        self.fold(T::default(), f)
    }

    /// Returns the sum of all elements
    /// which implement the `Add` trait in parallel for `Vec` type.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// assert_eq!(vec![1, 2, 3, 4].sum(), 10);
    /// ```
    fn sum(self) -> T where T: Sync + Copy + Default + Add<Output = T> {
        self.reduce(|a, b| a + b)
    }

    /// Returns the product of all elements
    /// which implement the `Product` trait in parallel for `Vec` type.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// assert_eq!(vec![1, 2, 3, 4].product(), 24);
    /// ```
    fn product(self) -> T where T: Product {
        self.into_par_iter().product()
    }

    /// Splits the original `Vec` into a couple of `Vec` according to the condition,
    /// where first `Vec` contains elements for which predicate yielded true,
    /// while second `Vec` contains elements for which predicate yielded false.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// assert_eq!(vec![1, 2, 3, 4].partition(|i| i % 2 != 0), (vec![1, 3], vec![2, 4]));
    /// ```
    fn partition(self, f: impl Fn(&T) -> bool + Sync + Send) -> (Vec<T>, Vec<T>) {
        self.into_par_iter().partition(f)
    }

    /// Splits the original `Vec` into a triple of `Vec` according to the condition,
    /// where first `Vec` contains elements for first predicate yielded true,
    /// where second `Vec` contains elements for second predicate yielded true,
    /// while third `Vec` contains elements for which two predicates yielded false.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// assert_eq!(vec![1, 2, 3].partition3(|i| i < &2, |i| i == &2), (vec![1], vec![2], vec![3]));
    /// ```
    fn partition3(self, predicate1: impl Fn(&T) -> bool + Sync + Send, predicate2: impl Fn(&T) -> bool + Sync + Send) -> (Vec<T>, Vec<T>, Vec<T>) where T: Sync {
        let ((first, second), third) = self.into_par_iter().partition_map(|e|
            if predicate1(&e) { Either::Left(Either::Left(e)) }
            else if predicate2(&e) { Either::Left(Either::Right(e)) }
            else { Either::Right(e) }
        );
        (first, second, third)
    }
}