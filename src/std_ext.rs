use std::{fmt::Debug, ops::Add, iter::Product};
use rayon::{iter::Either, prelude::*};

/// This trait is to implement some extension functions,
/// which need a generic return type, for any sized type.
pub trait KtStd<R>: Sized {
    /// Performs operation `f` with `&self`, returns the closure result.
    ///
    /// Moves environment variable(s) to closure by default.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// String::from("Hello")
    ///     .let_ref(|s| format!("String is: {}", s))
    ///     .echo();
    /// ```
    fn let_ref<'a>(&'a self, f: impl FnOnce(&'a Self) -> R) -> R {
        f(self)
    }

    /// Performs operation `f` with `&mut self`, returns the closure result.
    ///
    /// Moves environment variable(s) to closure by default.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// vec!["a", "b", "c"]
    ///     .let_mut(|v| { v.push("d"); format!("Vector is: {:?}", v) })
    ///     .echo();
    /// ```
    fn let_mut<'a>(&'a mut self, f: impl FnOnce(&'a mut Self) -> R) -> R {
        f(self)
    }

    /// Consumes `self`, performs operation `f` with it, returns the closure result.
    ///
    /// Moves environment variable(s) to closure by default.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// vec![9, 5, 3, 6, 1]
    ///     .let_owned(|v| v.sort()) // parallel sort, return self
    ///     .echo();
    /// ```
    fn let_owned(self, f: impl FnOnce(Self) -> R) -> R {
        f(self)
    }

    /// Consumes `self`, performs operation `f` with it, returns the receiver.
    ///
    /// Moves environment variable(s) to closure by default.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// vec!["Hello", "Rust"]
    ///     .also_ref(|v| println!("Vector is: {:?}", v))
    ///     .for_each(|s| s.echo());
    /// ```
    fn also_ref(self, f: impl FnOnce(&Self) -> R) -> Self {
        f(&self);
        self
    }
    
    /// Consumes `self`, performs operation `f` on it, returns the updated value.
    ///
    /// Moves environment variable(s) to closure by default.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// vec!["Hello", "Kotlin"]
    ///     .also_mut(|v| v[1] = "Rust")
    ///     .echo();
    /// ```
    fn also_mut(mut self, f: impl FnOnce(&mut Self) -> R) -> Self {
        f(&mut self);
        self
    }

    /// The Y Combinator
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// fn fact(n: usize) -> usize {
    ///     n.y(|f, n| match n {
    ///         0 | 1 => 1,
    ///         n => n * f(n - 1),
    ///     })
    /// }
    /// assert_eq!(fact(5), 5 * 4 * 3 * 2 * 1);
    ///
    /// fn fibonacci(n: usize) -> usize {
    ///     n.y(|f, n| match n {
    ///         0 => 0,
    ///         1 => 1,
    ///         n => f(n - 1) + f(n - 2),
    ///     })
    /// }
    /// assert_eq!(fibonacci(10), 55);
    /// ```
    fn y(self, f: impl Copy + Fn(&dyn Fn(Self) -> R, Self) -> R) -> R {
        use super::std_fun::y;
        y(f)(self)
    }
}

impl<T, R> KtStd<R> for T {}

/// This trait is to implement some extension functions for any sized type.
pub trait Ext: Sized {
    /// Chainable `drop`
    fn drop(self) {}

    /// System output -> with `:#?`'s `println!`.
    ///
    /// Consumes `self`, `println!` with `:#?`, returns `self`.
    fn sout(self) -> Self where Self: Debug {
        self.also_ref(|s| println!("{:#?}", s))
    }

    /// Consumes `self`, `println!` as it is, returns `self`.
    fn echo(self) -> Self where Self: Debug {
        self.also_ref(|s| println!("{:?}", s))
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

impl<T> Ext for T {}

/// This trait is to implement some extension functions for `bool` type.
pub trait BoolExt<R> {
    fn if_true(self, f: impl FnOnce() -> R) -> Option<R>;
    fn if_false(self, f: impl FnOnce() -> R) -> Option<R>;
}

impl<R> BoolExt<R> for bool {
    /// Chainable `if`, execute when the condition is `true`
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// let s = "Hello World";
    /// assert_eq!(Some("lo Wo"), s.starts_with("Hel").if_true(|| &s[3..8]));
    /// assert_eq!(None, s.starts_with("Wor").if_true(|| &s[3..8]));
    /// ```
    fn if_true(self, f: impl FnOnce() -> R) -> Option<R> {
        if self { Some(f()) } else { None }
    }

    /// Chainable `if`, execute when the condition is `false`
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// let s = "Hello World";
    /// assert_eq!(None, s.starts_with("Hel").if_false(|| &s[3..8]));
    /// assert_eq!(Some("lo Wo"), s.starts_with("Wor").if_false(|| &s[3..8]));
    /// ```
    fn if_false(self, f: impl FnOnce() -> R) -> Option<R> {
        if !self { Some(f()) } else { None }
    }
}

/// This trait is to implement some extension functions for `u128` type.
pub trait U128Ext {
    fn fmt_size_from(self, unit: char) -> String;
}

impl U128Ext for u128 {
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
pub trait FnOnceExt<P1, P2, R> {
    fn partial2(self, p2: P2) -> Box<dyn FnOnce(P1) -> R>;
}

impl<P1, P2: 'static, R, F> FnOnceExt<P1, P2, R> for F where F: FnOnce(P1, P2) -> R + 'static {
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

pub trait Sort<T> {
    fn sort(self) -> Vec<T>;
}

impl<T: Ord + Send> Sort<T> for Vec<T> {
    /// Sorts `Vec` in parallel.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::std_ext::*;
    ///
    /// vec![7, 4, 9, 2].sort().echo();
    /// ```
    fn sort(self) -> Vec<T> {
        self.also_mut(|v| v.par_sort())
    }
}

/// This trait is to implement some extension functions for `Vec` type,
/// which need two generic types and reference.
pub trait VecExt2<'a, T, R> where T: 'a {
    fn map(&'a self, f: impl Fn(&'a T) -> R + Sync + Send) -> Vec<R>;
    fn filter_map(&'a self, f: impl Fn(&'a T) -> Option<R> + Sync + Send) -> Vec<R>;
}

impl<'a, T, R> VecExt2<'a, T, R> for Vec<T> where T: 'a + Sync, R: Send {
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
    /// vec!["apple", "1", "banana", "2"]
    ///     .filter_map(|s| s.parse::<u8>().ok())
    ///     .let_owned(|v| assert_eq!(v, vec![1, 2]));
    /// ```
    fn filter_map(&'a self, f: impl Fn(&'a T) -> Option<R> + Sync + Send) -> Vec<R> {
        self.par_iter().filter_map(f).collect()
    }
}

/// This trait is to implement some extension functions for `Vec` type,
/// which need one generic type, and do not need reference.
pub trait VecExt1<T> {
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

impl<T> VecExt1<T> for Vec<T> where T: Send {
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