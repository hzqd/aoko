use core::marker::PhantomData;

pub trait Functor<T> {
    type Type<A>;

    fn fmap<U>(value: Self::Type<T>, f: impl FnMut(T) -> U) -> Self::Type<U>;
}

pub trait Applicative<T>: Functor<T> {
    fn pure(inner: T) -> Self::Type<T>;

    fn apply<U>(value: Self::Type<T>, f: Self::Type<impl FnMut(T) -> U>) -> Self::Type<U>;
}

pub trait Monad<T>: Applicative<T> {
    fn bind<U>(value: Self::Type<T>, f: impl FnMut(T) -> Self::Type<U>) -> Self::Type<U>;
}

pub struct Maybe;

impl<T> Functor<T> for Maybe {
    type Type<A> = Option<A>;

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
    fn fmap<U>(value: Self::Type<T>, f: impl FnMut(T) -> U) -> Self::Type<U> {
        value.map(f)
    }
}

impl<T> Applicative<T> for Maybe {
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
    fn pure(inner: T) -> Self::Type<T> {
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
    fn apply<U>(value: Self::Type<T>, f: Self::Type<impl FnMut(T) -> U>) -> Self::Type<U> {
        value.zip(f).map(|(v, mut f)| f(v))
    }
}

impl<T> Monad<T> for Maybe {
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
    fn bind<U>(value: Self::Type<T>, f: impl FnMut(T) -> Self::Type<U>) -> Self::Type<U> {
        value.and_then(f)
    }
}

pub struct Either<E>(PhantomData<E>);

impl<T, E> Functor<T> for Either<E> {
    type Type<A> = Result<A, E>;

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
    fn fmap<U>(value: Self::Type<T>, f: impl FnMut(T) -> U) -> Self::Type<U> {
        value.map(f)
    }
}

impl<T, E> Applicative<T> for Either<E> {
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
    fn pure(inner: T) -> Self::Type<T> {
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
    fn apply<U>(value: Self::Type<T>, f: Self::Type<impl FnMut(T) -> U>) -> Self::Type<U> {
        use super::ext::ResultExt;
        value.zip(f).map(|(v, mut f)| f(v))
    }
}

impl<T, E> Monad<T> for Either<E> {
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
    fn bind<U>(value: Self::Type<T>, f: impl FnMut(T) -> Self::Type<U>) -> Self::Type<U> {
        value.and_then(f)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Id<T>(pub T);

impl<T> Functor<T> for Id<T> {
    type Type<A> = Id<A>;

    /// # Examples
    /// 
    /// ```
    /// use aoko::no_std::functions::fam::*;
    /// 
    /// let id  = Id(23);
    /// let res = Id::fmap(id, |x| x - 20);
    /// assert_eq!(Id(3), res);
    /// ```
    fn fmap<U>(value: Self::Type<T>, mut f: impl FnMut(T) -> U) -> Self::Type<U> {
        Id(f(value.0))
    }
}

impl<T> Applicative<T> for Id<T> {
    /// # Examples
    /// 
    /// ```
    /// use aoko::no_std::functions::fam::*;
    /// 
    /// assert_eq!(Id(0), Id::pure(0));
    /// ```
    fn pure(inner: T) -> Id<T> {
        Id(inner)
    }

    /// # Examples
    /// 
    /// ```
    /// use aoko::no_std::functions::fam::*;
    /// 
    /// let id  = Id(23);
    /// let res = Id::apply(id, Id(|x| x - 20));
    /// assert_eq!(Id(3), res);
    /// ```
    fn apply<U>(value: Self::Type<T>, mut f: Self::Type<impl FnMut(T) -> U>) -> Self::Type<U> {
        Id(f.0(value.0))
    }
}

impl<T> Monad<T> for Id<T> {
    /// # Examples
    /// 
    /// ```
    /// use aoko::no_std::functions::fam::*;
    /// 
    /// let id  = Id(23);
    /// let res = Id::bind(id, |x| Id(x - 20));
    /// assert_eq!(Id(3), res);
    /// ```
    fn bind<U>(value: Self::Type<T>, mut f: impl FnMut(T) -> Self::Type<U>) -> Self::Type<U> {
        f(value.0)
    }
}