use crate::no_std::ext::AnyExt1;
use std::{prelude::v1::*, iter::Product, ops::Add};
use rayon::{iter::Either, prelude::*};

pub trait StdSort<T> {
    fn sort(self) -> Vec<T>;
}

impl<T: Ord + Send> StdSort<T> for Vec<T> {
    /// Sorts `Vec` in parallel.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::standard::par::*;
    ///
    /// let v = vec![7, 4, 9, 2].sort();
    /// assert_eq!(v, vec![2, 4, 7, 9]);
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
    /// use aoko::standard::par::*;
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
    /// use aoko::standard::par::*;
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
    /// use aoko::standard::{par::*, ext::*};
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
    /// use aoko::standard::{par::*, ext::*};
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
    /// use aoko::standard::par::*;
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
    /// use aoko::standard::par::*;
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
    /// use aoko::standard::par::*;
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
    /// use aoko::standard::par::*;
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
    /// use aoko::standard::par::*;
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
    /// use aoko::standard::par::*;
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
    /// use aoko::standard::par::*;
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