/*! # Universal Suffix Calls

This module provides a single trait, `Pipe`, which provides a number of methods
useful for placing functions in suffix position. The most common method, `pipe`,
forwards a value `T` into any function `T -> R`, returning `R`. The other
methods all apply some form of borrowing to the value before passing the borrow
into the piped function. These are of less value, but provided to maintain a
similar API to the `pipeline` module’s methods, and for convenience in the event that
you do have a use for them.

This module is as much of a [UFCS] method syntax that can be provided as a
library, rather than in the language grammar.

[UFCS]: https://en.wikipedia.org/wiki/Uniform_Function_Call_Syntax
!*/

use core::{
	borrow::{Borrow, BorrowMut},
	ops::{Deref, DerefMut},
};

/** Provides universal suffix-position call syntax for any function.

This trait provides methods that allow any closure or free function to be placed
as a suffix-position call, by writing them as

```rust
# use aoko::no_std::pipelines::pipe::Pipe;
# let receiver = 5;
fn not_a_method(x: i32) -> u8 { x as u8 }
receiver.pipe(not_a_method);
```

Piping into functions that take more than one argument still requires writing a
closure with ordinary function-call syntax. This is after all only a library,
not a syntax transformation:

```rust
use aoko::no_std::pipelines::pipe::Pipe;
fn add(x: i32, y: i32) -> i32 { x + y }

let out = 5.pipe(|x| add(x, 10));
assert_eq!(out, 15);
```

Like tapping, piping is useful for cases where you want to write a sequence of
processing steps without introducing many intermediate bindings, and your steps
contain functions which are not eligible for dot-call syntax.

The main difference between piping and tapping is that tapping always returns
the value that was passed into the pipeline, while piping forwards the value into the
effect function, and returns the output of evaluating the effect function with
the value. Piping is a transformation, not merely an inspection or modification.
**/
pub trait Pipe<R> {
	/// Pipes by value. This is generally the method you want to use.
	///
	/// # Examples
	///
	/// ```rust
	/// use aoko::no_std::pipelines::pipe::Pipe;
	///
	/// fn triple(x: i32) -> i64 {
	///   x as i64 * 3
	/// }
	///
	/// assert_eq!(
	///   10.pipe(triple),
	///   30,
	/// );
	/// ```
	#[inline(always)]
	fn pipe(self, f: impl FnOnce(Self) -> R) -> R where Self: Sized {
		f(self)
	}

	/// Borrows `self` and passes that borrow into the pipe function.
	///
	/// # Examples
	///
	/// ```rust
	/// use aoko::no_std::pipelines::pipe::Pipe;
	///
	/// fn fold(v: &Vec<i32>) -> i32 {
	///   v.iter().copied().sum()
	/// }
	/// let vec = vec![1, 2, 3, 4, 5];
	/// let sum = vec.pipe_ref(fold);
	/// assert_eq!(sum, 15);
	/// assert_eq!(vec.len(), 5);
	/// ```
	#[inline(always)]
	fn pipe_ref<'a>(&'a self, f: impl FnOnce(&'a Self) -> R) -> R {
		f(self)
	}

	/// Mutably borrows `self` and passes that borrow into the pipe function.
	///
	/// # Examples
	///
	/// ```rust
	/// use aoko::no_std::pipelines::pipe::Pipe;
	///
	/// let mut vec = vec![false, true];
	/// let last = vec
	///   .pipe_mut(Vec::pop)
	///   .pipe(Option::unwrap);
	/// assert!(last);
	/// ```
	///
	/// Both of these functions are eligible for method-call syntax, and should
	/// not be piped. Writing out non-trivial examples for these is a lot of
	/// boilerplate.
	#[inline(always)]
	fn pipe_mut<'a>(&'a mut self, f: impl FnOnce(&'a mut Self) -> R) -> R {
		f(self)
	}

	/// Borrows `self`, then passes `self.borrow()` into the pipe function.
	///
	/// # Examples
	///
	/// ```rust
	/// use std::borrow::Cow;
	/// use aoko::no_std::pipelines::pipe::Pipe;
	///
	/// let len = Cow::<'static, str>::from("hello, world")
	///   .pipe_borrow(str::len);
	/// assert_eq!(len, 12);
	/// ```
	#[inline(always)]
	fn pipe_borrow<'a, B>(&'a self, f: impl FnOnce(&'a B) -> R) -> R
	where
		Self: Borrow<B>,
		B: 'a + ?Sized,
	{
		f(Borrow::<B>::borrow(self))
	}

	/// Mutably borrows `self`, then passes `self.borrow_mut()` into the pipe
	/// function.
	///
	/// ```rust
	/// use aoko::no_std::pipelines::pipe::Pipe;
	///
	/// let mut txt = "hello, world".to_string();
	/// let ptr = txt
	///   .pipe_borrow_mut(str::as_mut_ptr);
	/// ```
	///
	/// This is a very contrived example, but the `BorrowMut` trait has almost
	/// no implementors in the standard library, and of the implementations
	/// available, there are almost no methods that fit this API.
	#[inline(always)]
	fn pipe_borrow_mut<'a, B>(&'a mut self, f: impl FnOnce(&'a mut B) -> R) -> R
	where
		Self: BorrowMut<B>,
		B: 'a + ?Sized,
	{
		f(BorrowMut::<B>::borrow_mut(self))
	}

	/// Borrows `self`, then passes `self.as_ref()` into the pipe function.
	#[inline(always)]
	fn pipe_as_ref<'a, U>(&'a self, f: impl FnOnce(&'a U) -> R) -> R
	where
		Self: AsRef<U>,
		U: 'a + ?Sized,
	{
		f(AsRef::<U>::as_ref(self))
	}

	/// Mutably borrows `self`, then passes `self.as_mut()` into the pipe
	/// function.
	#[inline(always)]
	fn pipe_as_mut<'a, U>(&'a mut self, f: impl FnOnce(&'a mut U) -> R) -> R
	where
		Self: AsMut<U>,
		U: 'a + ?Sized,
	{
		f(AsMut::<U>::as_mut(self))
	}

	/// Borrows `self`, then passes `self.deref()` into the pipe function.
	#[inline(always)]
	fn pipe_deref<'a, T>(&'a self, f: impl FnOnce(&'a T) -> R) -> R
	where
		Self: Deref<Target = T>,
		T: 'a + ?Sized,
	{
		f(Deref::deref(self))
	}

	/// Mutably borrows `self`, then passes `self.deref_mut()` into the pipe
	/// function.
	#[inline(always)]
	fn pipe_deref_mut<'a, T>(&'a mut self, f: impl FnOnce(&'a mut T) -> R) -> R
	where
		Self: DerefMut + Deref<Target = T>,
		T: 'a + ?Sized,
	{
		f(DerefMut::deref_mut(self))
	}
}

impl<T, R> Pipe<R> for T where T: ?Sized {}