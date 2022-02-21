/*! # Point-Free Inspection
The standard library does not provide a way to view or modify an expression
without binding it to a name. This module provides extension methods that take
and return a value, allowing it to be temporarily bound without creating a new
`let`-statement in the enclosing scope.
The two main uses of these methods are to temporarily attach debugging
tracepoints to an expression without modifying its surrounding code, or to
temporarily mutate an otherwise-immutable object.
For convenience, methods are available that will modify the *view* of the tapped
object that is passed to the effect function, by using the value’s
`Borrow`/`BorrowMut`, `AsRef`/`AsMut`, or `Index`/`IndexMut` trait
implementations. For example, the `Vec` collection has no `fn sort` method: this
is actually implemented on slices, to which `Vec` dereferences.
```rust
use aoko::no_std::pipelines::tap::*;
# fn make_vec() -> Vec<i32> { vec![] }
// taps take ordinary closures, which can use deref coercion
make_vec().tap_mut(|v| v.sort());
// `Vec<T>` implements `BorrowMut<[T]>`,
make_vec().tap_borrow_mut(<[_]>::sort);
// and `AsMut<[T]>`,
make_vec().tap_as_mut(<[_]>::sort);
// and `DerefMut<Target = [T]>,
make_vec().tap_deref_mut(<[_]>::sort);
// but has no inherent method `sort`.
// make_vec().tap_mut(Vec::sort);
```
!*/

use core::{
	borrow::{Borrow, BorrowMut},
	ops::{Deref, DerefMut},
};

/** Point-free value inspection and modification.
This trait provides methods that permit viewing the value of an expression
without requiring a new `let` binding or any other alterations to the original
code other than insertion of the `.tap()` call.
The methods in this trait do not perform any view conversions on the value they
receive; it is borrowed and passed directly to the effect argument.
 **/
pub trait Tap<Ret>: Sized {
	/// Immutable access to a value.
	///
	/// This function permits a value to be viewed by some inspecting function
	/// without affecting the overall shape of the expression that contains this
	/// method call. It is useful for attaching assertions or logging points
	/// into a multi-part expression.
	///
	/// # Examples
	///
	/// Here we use `.tap()` to attach logging tracepoints to each stage of a
	/// value-processing pipeline.
	///
	/// ```rust
	/// use aoko::no_std::pipelines::tap::Tap;
	/// # struct Tmp;
	/// # impl Tmp { fn process_value(self) -> Self { self } }
	/// # fn make_value() -> Tmp { Tmp }
	/// # macro_rules! log { ($msg:literal, $x:ident) => {{}}; }
	///
	/// let end = make_value()
	///   // this line has no effect on the rest of the code
	///   .tap(|v| log!("The produced value was: {}", v))
	///   .process_value();
	/// ```
	#[inline(always)]
	fn tap(self, func: impl FnOnce(&Self) -> Ret) -> Self {
		func(&self);
		self
	}

	/// Mutable access to a value.
	///
	/// This function permits a value to be modified by some function without
	/// affecting the overall shape of the expression that contains this method
	/// call. It is useful for attaching modifier functions that have an
	/// `&mut Self -> ()` signature to an expression, without requiring an
	/// explicit `let mut` binding.
	///
	/// # Examples
	///
	/// Here we use `.tap_mut()` to sort an array without requiring multiple
	/// bindings.
	///
	/// ```rust
	/// use aoko::no_std::pipelines::tap::Tap;
	///
	/// let sorted = [1i32, 5, 2, 4, 3]
	///   .tap_mut(|arr| arr.sort());
	/// assert_eq!(sorted, [1, 2, 3, 4, 5]);
	/// ```
	///
	/// Without tapping, this would be written as
	///
	/// ```rust
	/// let mut received = [1, 5, 2, 4, 3];
	/// received.sort();
	/// let sorted = received;
	/// ```
	///
	/// The mutable tap is a convenient alternative when the expression to
	/// produce the collection is more complex, for example, an iterator
	/// pipeline collected into a vector.
	#[inline(always)]
	fn tap_mut(mut self, func: impl FnOnce(&mut Self) -> Ret) -> Self {
		func(&mut self);
		self
	}

	/// Immutable access to the `Borrow<B>` of a value.
	///
	/// This function is identical to [`Tap::tap`], except that the effect
	/// function receives an `&B` produced by `Borrow::<B>::borrow`, rather than
	/// an `&Self`.
	///
	/// [`Tap::tap`]: trait.Tap.html#method.tap
	#[inline(always)]
	fn tap_borrow<B>(self, func: impl FnOnce(&B) -> Ret) -> Self
		where
			Self: Borrow<B>,
			B: ?Sized,
	{
		func(Borrow::<B>::borrow(&self));
		self
	}

	/// Mutable access to the `BorrowMut<B>` of a value.
	///
	/// This function is identical to [`Tap::tap_mut`], except that the effect
	/// function receives an `&mut B` produced by `BorrowMut::<B>::borrow_mut`,
	/// rather than an `&mut Self`.
	///
	/// [`Tap::tap_mut`]: trait.Tap.html#method.tap_mut
	#[inline(always)]
	fn tap_borrow_mut<B>(mut self, func: impl FnOnce(&mut B) -> Ret) -> Self
		where
			Self: BorrowMut<B>,
			B: ?Sized,
	{
		func(BorrowMut::<B>::borrow_mut(&mut self));
		self
	}

	/// Immutable access to the `AsRef<R>` view of a value.
	///
	/// This function is identical to [`Tap::tap`], except that the effect
	/// function receives an `&R` produced by `AsRef::<R>::as_ref`, rather than
	/// an `&Self`.
	///
	/// [`Tap::tap`]: trait.Tap.html#method.tap
	#[inline(always)]
	fn tap_as_ref<R>(self, func: impl FnOnce(&R) -> Ret) -> Self
		where
			Self: AsRef<R>,
			R: ?Sized,
	{
		func(AsRef::<R>::as_ref(&self));
		self
	}

	/// Mutable access to the `AsMut<R>` view of a value.
	///
	/// This function is identical to [`Tap::tap_mut`], except that the effect
	/// function receives an `&mut R` produced by `AsMut::<R>::as_mut`, rather
	/// than an `&mut Self`.
	///
	/// [`Tap::tap_mut`]: trait.Tap.html#method.tap_mut
	#[inline(always)]
	fn tap_as_mut<R>(mut self, func: impl FnOnce(&mut R) -> Ret) -> Self
		where
			Self: AsMut<R>,
			R: ?Sized,
	{
		func(AsMut::<R>::as_mut(&mut self));
		self
	}

	/// Immutable access to the `Deref::Target` of a value.
	///
	/// This function is identical to [`Tap::tap`], except that the effect
	/// function receives an `&Self::Target` produced by `Deref::deref`, rather
	/// than an `&Self`.
	///
	/// [`Tap::tap`]: trait.Tap.html#method.tap
	#[inline(always)]
	fn tap_deref<T>(self, func: impl FnOnce(&T) -> Ret) -> Self
		where
			Self: Deref<Target = T>,
			T: ?Sized,
	{
		func(Deref::deref(&self));
		self
	}

	/// Mutable access to the `Deref::Target` of a value.
	///
	/// This function is identical to [`Tap::tap_mut`], except that the effect
	/// function receives an `&mut Self::Target` produced by
	/// `DerefMut::deref_mut`, rather than an `&mut Self`.
	///
	/// [`Tap::tap_mut`]: trait.Tap.html#method.tap_mut
	#[inline(always)]
	fn tap_deref_mut<T>(mut self, func: impl FnOnce(&mut T) -> Ret) -> Self
		where
			Self: DerefMut + Deref<Target = T>,
			T: ?Sized,
	{
		func(DerefMut::deref_mut(&mut self));
		self
	}

	//  debug-build-only copies of the above methods

	/// Calls `.tap()` only in debug builds, and is erased in release builds.
	#[inline(always)]
	fn tap_dbg(self, func: impl FnOnce(&Self) -> Ret) -> Self {
		if cfg!(debug_assertions) {
			func(&self);
		}
		self
	}

	/// Calls `.tap_mut()` only in debug builds, and is erased in release
	/// builds.
	#[inline(always)]
	fn tap_mut_dbg(mut self, func: impl FnOnce(&mut Self) -> Ret) -> Self {
		if cfg!(debug_assertions) {
			func(&mut self);
		}
		self
	}

	/// Calls `.tap_borrow()` only in debug builds, and is erased in release
	/// builds.
	#[inline(always)]
	fn tap_borrow_dbg<B>(self, func: impl FnOnce(&B) -> Ret) -> Self
		where
			Self: Borrow<B>,
			B: ?Sized,
	{
		if cfg!(debug_assertions) {
			func(Borrow::<B>::borrow(&self));
		}
		self
	}

	/// Calls `.tap_borrow_mut()` only in debug builds, and is erased in release
	/// builds.
	#[inline(always)]
	fn tap_borrow_mut_dbg<B>(mut self, func: impl FnOnce(&mut B) -> Ret) -> Self
		where
			Self: BorrowMut<B>,
			B: ?Sized,
	{
		if cfg!(debug_assertions) {
			func(BorrowMut::<B>::borrow_mut(&mut self));
		}
		self
	}

	/// Calls `.tap_as_ref()` only in debug builds, and is erased in release
	/// builds.
	#[inline(always)]
	fn tap_as_ref_dbg<R>(self, func: impl FnOnce(&R) -> Ret) -> Self
		where
			Self: AsRef<R>,
			R: ?Sized,
	{
		if cfg!(debug_assertions) {
			func(AsRef::<R>::as_ref(&self));
		}
		self
	}

	/// Calls `.tap_as_mut()` only in debug builds, and is erased in release
	/// builds.
	#[inline(always)]
	fn tap_as_mut_dbg<R>(mut self, func: impl FnOnce(&mut R) -> Ret) -> Self
		where
			Self: AsMut<R>,
			R: ?Sized,
	{
		if cfg!(debug_assertions) {
			func(AsMut::<R>::as_mut(&mut self));
		}
		self
	}

	/// Calls `.tap_deref()` only in debug builds, and is erased in release
	/// builds.
	#[inline(always)]
	fn tap_deref_dbg<T>(self, func: impl FnOnce(&T) -> Ret) -> Self
		where
			Self: Deref<Target = T>,
			T: ?Sized,
	{
		if cfg!(debug_assertions) {
			func(Deref::deref(&self));
		}
		self
	}

	/// Calls `.tap_deref_mut()` only in debug builds, and is erased in release
	/// builds.
	#[inline(always)]
	fn tap_deref_mut_dbg<T>(mut self, func: impl FnOnce(&mut T) -> Ret) -> Self
		where
			Self: DerefMut + Deref<Target = T>,
			T: ?Sized,
	{
		if cfg!(debug_assertions) {
			func(DerefMut::deref_mut(&mut self));
		}
		self
	}
}

impl<T, R> Tap<R> for T where T: Sized {}

/** Optional tapping, conditional on the optional presence of a value.
This trait is intended for use on types that express the concept of “optional
presence”, primarily the [`Option`] monad. It provides taps that inspect the
container to determine if the effect function should execute or not.
> Note: This trait is a specialization of [`TapFallible`], and exists because
> the [`std::ops::Try`] trait is still unstable. When `Try` stabilizes, this
> trait can be removed, and `TapFallible` blanket-applied to all `Try`
> implementors.
[`Option`]: https://doc.rust-lang.org/std/option/enum.Option.html
[`TapFallible`]: trait.TapFallible.html
[`std::ops::Try`]: https://doc.rust-lang.org/std/ops/trait.Try.html
 **/
pub trait TapOptional<R>: Sized {
	/// The interior type that the container may or may not carry.
	type Val: ?Sized;

	/// Immutably accesses the contained value element when present, passing the value on.
	///
	/// This function is identical to [`Tap::tap`], except that it is required
	/// to check the implementing container for value presence before running.
	/// Implementors must not run the effect function if the container is marked
	/// as being empty.
	///
	/// [`Tap::tap`]: trait.Tap.html#method.tap
	///
	/// # Examples
	/// ```rust
	/// use aoko::no_std::pipelines::tap::TapOptional;
	///
	/// let (some, none) = (Some(10), None::<i32>);
	/// assert_eq!(some.tap_some(|x| println!("Some({})", x)), some); // Prints `Some(10)`.
	/// assert_eq!(none.tap_some(|x| println!("Some({})", x)), none); // Prints nothing.
	/// ```
	fn tap_some(self, func: impl FnOnce(&Self::Val) -> R) -> Self;

	/// Mutably accesses the contained value element when present, passing the value on.
	///
	/// This function is identical to [`Tap::tap_mut`], except that it is
	/// required to check the implementing container for value presence before
	/// running. Implementors must not run the effect function if the container
	/// is marked as being empty.
	///
	/// [`Tap::tap_mut`]: trait.Tap.html#method.tap_mut
	///
	/// # Examples
	/// ```rust
	/// use aoko::no_std::pipelines::tap::TapOptional;
	///
	/// let (some, none) = (Some(10), None::<i32>);
	/// assert_eq!(some.tap_some_mut(|x| *x += 1), Some(11));
	/// assert_eq!(none.tap_some_mut(|x| *x += 1), none);
	/// ```
	fn tap_some_mut(self, func: impl FnOnce(&mut Self::Val) -> R) -> Self;

	/// Runs a side effect when the contained value element is absent, passing the value on.
	///
	/// This function is identical to [`Tap::tap`], except that it is required
	/// to check the implementing container for value absence before running.
	/// Implementors must not run the effect function if the container is marked
	/// as being non-empty.
	///
	/// [`Tap::tap`]: trait.Tap.html#method.tap
	///
	/// # Examples
	/// ```rust
	/// use aoko::no_std::pipelines::tap::TapOptional;
	///
	/// let mut x = 0;
	///
	/// Some(10).tap_none(|| x += 1); // This does nothing.
	/// assert_eq!(x, 0);
	///
	/// None::<i32>.tap_none(|| x += 1); // This increments x.
	/// assert_eq!(x, 1);
	/// ```
	fn tap_none(self, func: impl FnOnce() -> R) -> Self;

	/// Calls `.tap_some()` only in debug builds, and is erased in release
	/// builds.
	#[inline(always)]
	fn tap_some_dbg(self, func: impl FnOnce(&Self::Val) -> R) -> Self {
		if cfg!(debug_assertions) {
			self.tap_some(func)
		} else {
			self
		}
	}

	/// Calls `.tap_some_mut()` only in debug builds, and is erased in release
	/// builds.
	#[inline(always)]
	fn tap_some_mut_dbg(self, func: impl FnOnce(&mut Self::Val) -> R) -> Self {
		if cfg!(debug_assertions) {
			self.tap_some_mut(func)
		} else {
			self
		}
	}

	/// Calls `.tap_none()` only in debug builds, and is erased in release
	/// builds.
	#[inline(always)]
	fn tap_none_dbg(self, func: impl FnOnce() -> R) -> Self {
		if cfg!(debug_assertions) {
			self.tap_none(func)
		} else {
			self
		}
	}
}

impl<T, R> TapOptional<R> for Option<T> {
	type Val = T;

	#[inline(always)]
	fn tap_some(self, func: impl FnOnce(&T) -> R) -> Self {
		if let Some(ref val) = self {
			func(val);
		}
		self
	}

	#[inline(always)]
	fn tap_some_mut(mut self, func: impl FnOnce(&mut T) -> R) -> Self {
		if let Some(ref mut val) = self {
			func(val);
		}
		self
	}

	#[inline(always)]
	fn tap_none(self, func: impl FnOnce() -> R) -> Self {
		if self.is_none() {
			func();
		}
		self
	}
}

/** Fallible tapping, conditional on the optional success of an expression.
This trait is intended for use on types that express the concept of “fallible
presence”, primarily the [`Result`] monad. It provides taps that inspect the
container to determine if the effect function should execute or not.
> Note: This trait would ideally be implemented as a blanket over all
> [`std::ops::Try`] implementors. When `Try` stabilizes, this crate can be
> updated to do so.
[`Result`]: https://doc.rust-lang.org/std/result/enum.Result.html
[`std::ops::Try`]: https://doc.rust-lang.org/std/ops/trait.Try.html
 **/
pub trait TapFallible<R>: Sized {
	/// The interior type used to indicate a successful construction.
	type Ok: ?Sized;

	/// The interior type used to indicate a failed construction.
	type Err: ?Sized;

	/// Immutably accesses the contained `Ok` value element of a fallible container, passing the value on.
	///
	/// This function is identical to [`Tap::tap`], except that it is required
	/// to check the implementing container for value success before running.
	/// Implementors must not run the effect function if the container is marked
	/// as being a failure.
	///
	/// [`Tap::tap`]: trait.Tap.html#method.tap
	///
	/// # Examples
	/// ```rust
	/// use aoko::no_std::pipelines::tap::TapFallible;
	///
	/// let (ok, err) = (Ok::<i32, i32>(10), Err::<i32, i32>(10));
	/// assert_eq!(ok.tap_ok(|x| println!("Ok({})", x)), ok); // Prints `Ok(10)`.
	/// assert_eq!(err.tap_ok(|x| println!("Ok({})", x)), err); // Prints nothing.
	/// ```
	fn tap_ok(self, func: impl FnOnce(&Self::Ok) -> R) -> Self;

	/// Mutably accesses the contained `Ok` value element of a fallible container, passing the value on.
	///
	/// This function is identical to [`Tap::tap_mut`], except that it is
	/// required to check the implementing container for value success before
	/// running. Implementors must not run the effect function if the container
	/// is marked as being a failure.
	///
	/// [`Tap::tap_mut`]: trait.Tap.html#method.tap_mut
	///
	/// # Examples
	/// ```rust
	/// use aoko::no_std::pipelines::tap::TapFallible;
	///
	/// let (ok, err) = (Ok::<i32, i32>(10), Err::<i32, i32>(10));
	/// assert_eq!(ok.tap_ok_mut(|x| *x += 1), Ok(11));
	/// assert_eq!(err.tap_ok_mut(|x| *x += 1), Err(10));
	/// ```
	fn tap_ok_mut(self, func: impl FnOnce(&mut Self::Ok) -> R) -> Self;

	/// Immutably accesses the contained `Err` value element of a fallible container, passing the value on.
	///
	/// This function is identical to [`Tap::tap`], except that it is required
	/// to check the implementing container for value failure before running.
	/// Implementors must not run the effect function if the container is marked
	/// as being a success.
	///
	/// [`Tap::tap`]: trait.Tap.html#method.tap
	///
	//
	/// # Examples
	/// ```rust
	/// use aoko::no_std::pipelines::tap::TapFallible;
	///
	/// let (ok, err) = (Ok::<i32, i32>(10), Err::<i32, i32>(10));
	/// assert_eq!(err.tap_err(|x| println!("Err({})", x)), err); // Prints `Err(10)`.
	/// assert_eq!(ok.tap_err(|x| println!("Err({})", x)), ok); // Prints nothing.
	/// ```
	fn tap_err(self, func: impl FnOnce(&Self::Err) -> R) -> Self;

	/// Mutably accesses the contained `Err` value element of a fallible container, passing the value on.
	///
	/// This function is identical to [`Tap::tap_mut`], except that it is
	/// required to check the implementing container for value failure before
	/// running. Implementors must not run the effect function if the container
	/// is marked as being a success.
	///
	/// [`Tap::tap_mut`]: trait.Tap.html#method.tap_mut
	/// # Examples
	/// ```rust
	/// use aoko::no_std::pipelines::tap::TapFallible;
	///
	/// let (ok, err) = (Ok::<i32, i32>(10), Err::<i32, i32>(10));
	/// assert_eq!(err.tap_err_mut(|x| *x += 1), Err(11));
	/// assert_eq!(ok.tap_err_mut(|x| *x += 1), Ok(10));
	/// ```
	fn tap_err_mut(self, func: impl FnOnce(&mut Self::Err) -> R) -> Self;

	/// Calls `.tap_ok()` only in debug builds, and is erased in release builds.
	#[inline(always)]
	fn tap_ok_dbg(self, func: impl FnOnce(&Self::Ok) -> R) -> Self {
		if cfg!(debug_assertions) {
			self.tap_ok(func)
		} else {
			self
		}
	}

	/// Calls `.tap_ok_mut()` only in debug builds, and is erased in release
	/// builds.
	#[inline(always)]
	fn tap_ok_mut_dbg(self, func: impl FnOnce(&mut Self::Ok) -> R) -> Self {
		if cfg!(debug_assertions) {
			self.tap_ok_mut(func)
		} else {
			self
		}
	}

	/// Calls `.tap_err()` only in debug builds, and is erased in release
	/// builds.
	#[inline(always)]
	fn tap_err_dbg(self, func: impl FnOnce(&Self::Err) -> R) -> Self {
		if cfg!(debug_assertions) {
			self.tap_err(func)
		} else {
			self
		}
	}

	/// Calls `.tap_err_mut()` only in debug builds, and is erased in release
	/// builds.
	#[inline(always)]
	fn tap_err_mut_dbg(self, func: impl FnOnce(&mut Self::Err) -> R) -> Self {
		if cfg!(debug_assertions) {
			self.tap_err_mut(func)
		} else {
			self
		}
	}
}

impl<T, E, R> TapFallible<R> for Result<T, E> {
	type Ok = T;
	type Err = E;

	#[inline(always)]
	fn tap_ok(self, func: impl FnOnce(&T) -> R) -> Self {
		if let Ok(ref val) = self {
			func(val);
		}
		self
	}

	#[inline(always)]
	fn tap_ok_mut(mut self, func: impl FnOnce(&mut T) -> R) -> Self {
		if let Ok(ref mut val) = self {
			func(val);
		}
		self
	}

	#[inline(always)]
	fn tap_err(self, func: impl FnOnce(&E) -> R) -> Self {
		if let Err(ref val) = self {
			func(val);
		}
		self
	}

	#[inline(always)]
	fn tap_err_mut(mut self, func: impl FnOnce(&mut E) -> R) -> Self {
		if let Err(ref mut val) = self {
			func(val);
		}
		self
	}
}