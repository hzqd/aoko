use core::marker::PhantomData;

pub trait Functor {
    type Type<T>;

    fn fmap<T, U>(value: Self::Type<T>, f: impl FnMut(T) -> U) -> Self::Type<U>;
}

pub trait Applicative: Functor {
    fn pure<T>(inner: T) -> Self::Type<T>;

    fn apply<T, U>(value: Self::Type<T>, f: Self::Type<impl FnMut(T) -> U>) -> Self::Type<U>;
}

pub trait Monad: Applicative {
    fn bind<T, U>(value: Self::Type<T>, f: impl FnMut(T) -> Self::Type<U>) -> Self::Type<U>;
}

pub struct Maybe;

impl Functor for Maybe {
    type Type<T> = Option<T>;

    /// # Examples
    /// 
    /// ```
    /// use std::ops::Not;
    /// use aoko::{assert_eqs, no_std::functions::{fun::s, fam::*}};
    /// 
    /// assert_eqs! {
    ///     Some(1),         Maybe::fmap(0.into(), |x| x + 1);
    ///     Some(true),      Maybe::fmap(false.into(), |x| x.not());
    ///     Some(s("abcd")), Maybe::fmap(s("ab").into(), |x| x + "cd");
    /// }
    /// ```
    fn fmap<T, U>(value: Self::Type<T>, f: impl FnMut(T) -> U) -> Self::Type<U> {
        value.map(f)
    }
}

impl Applicative for Maybe {
    /// # Examples
    /// 
    /// ```
    /// use aoko::{assert_eqs, no_std::functions::fam::*};
    /// 
    /// assert_eqs! {
    ///     Some(0),    Maybe::pure(0);
    ///     Some(true), Maybe::pure(true);
    ///     Some("xy"), Maybe::pure("xy");
    /// }
    /// ```
    fn pure<T>(inner: T) -> Self::Type<T> {
        inner.into()
    }

    /// # Examples
    /// 
    /// ```
    /// use std::ops::Not;
    /// use aoko::{assert_eqs, no_std::functions::{fun::s, fam::*}};
    /// 
    /// assert_eqs! {
    ///     Some(1),         Maybe::apply(0.into(), Some(|x| x + 1));
    ///     Some(true),      Maybe::apply(false.into(), Some(|x: bool| x.not()));
    ///     Some(s("abcd")), Maybe::apply(s("ab").into(), Some(|x| x + "cd"));
    /// }
    /// ```
    fn apply<T, U>(value: Self::Type<T>, f: Self::Type<impl FnMut(T) -> U>) -> Self::Type<U> {
        value.zip(f).map(|(v, mut f)| f(v))
    }
}

impl Monad for Maybe {
    /// # Examples
    /// 
    /// ```
    /// use std::ops::Not;
    /// use aoko::{assert_eqs, no_std::functions::{fun::s, fam::*}};
    /// 
    /// assert_eqs! {
    ///     Some(1),         Maybe::bind(0.into(), |x| Some(x + 1));
    ///     Some(true),      Maybe::bind(false.into(), |x| x.not().into());
    ///     Some(s("abcd")), Maybe::bind(s("ab").into(), |x| Some(x + "cd"));
    /// }
    /// ```
    fn bind<T, U>(value: Self::Type<T>, f: impl FnMut(T) -> Self::Type<U>) -> Self::Type<U> {
        value.and_then(f)
    }
}

pub struct Either<E>(PhantomData<E>);

impl<E> Functor for Either<E> {
    type Type<T> = Result<T, E>;

    /// # Examples
    /// 
    /// ```
    /// use std::ops::Not;
    /// use aoko::{assert_eqs, no_std::functions::{fun::s, fam::*}};
    /// 
    /// assert_eqs! {
    ///     Ok::<_, ()>(1),         Either::fmap(Ok(0), |x| x + 1);
    ///     Ok::<_, ()>(true),      Either::fmap(Ok(false), |x| x.not());
    ///     Ok::<_, ()>(s("abcd")), Either::fmap(Ok(s("ab")), |x| x + "cd");
    /// }
    /// ```
    fn fmap<T, U>(value: Self::Type<T>, f: impl FnMut(T) -> U) -> Self::Type<U> {
        value.map(f)
    }
}

impl<E> Applicative for Either<E> {
    /// # Examples
    /// 
    /// ```
    /// use aoko::{assert_eqs, no_std::functions::fam::*};
    /// 
    /// assert_eqs! {
    ///     Ok::<_, ()>(0),    Either::pure(0);
    ///     Ok::<_, ()>(true), Either::pure(true);
    ///     Ok::<_, ()>("xy"), Either::pure("xy");
    /// }
    /// ```
    fn pure<T>(inner: T) -> Self::Type<T> {
        Result::from(Ok(inner))
    }

    /// # Examples
    /// 
    /// ```
    /// use std::ops::Not;
    /// use aoko::{assert_eqs, no_std::functions::{fun::s, fam::*}};
    /// 
    /// let mut f = Ok(|x| x + "cd");
    /// f = Err(());
    /// 
    /// assert_eqs! {
    ///     Ok::<_, ()>(0), Either::apply(Ok(0), Ok(|x| x / 1));
    ///     Err(-1),        Either::apply(Err(-1), Ok(|x: bool| x.not()));
    ///     Err(()),        Either::apply(Ok(s("ab")), f);
    /// }
    /// ```
    fn apply<T, U>(value: Self::Type<T>, f: Self::Type<impl FnMut(T) -> U>) -> Self::Type<U> {
        use super::ext::ResultExt;
        value.zip(f).map(|(v, mut f)| f(v))
    }
}

impl<E> Monad for Either<E> {
    /// # Examples
    /// 
    /// ```
    /// use std::ops::Not;
    /// use aoko::{assert_eqs, no_std::functions::{fun::s, fam::*}};
    /// 
    /// assert_eqs! {
    ///     Ok::<_, ()>(1),         Either::bind(Ok(0), |x| Ok(x + 1));
    ///     Ok::<_, ()>(true),      Either::bind(Ok(false), |x| Ok(x.not()));
    ///     Ok::<_, ()>(s("abcd")), Either::bind(Ok(s("ab")), |x| Ok(x + "cd"));
    /// }
    /// ```
    fn bind<T, U>(value: Self::Type<T>, f: impl FnMut(T) -> Self::Type<U>) -> Self::Type<U> {
        value.and_then(f)
    }
}