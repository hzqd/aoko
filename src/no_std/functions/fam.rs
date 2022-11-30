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

pub struct OptionType;

impl Functor for OptionType {
    type Type<T> = Option<T>;

    /// # Examples
    /// 
    /// ```
    /// use std::ops::Not;
    /// use aoko::{assert_eqs, no_std::functions::{fun::s, fam::*}};
    /// 
    /// assert_eqs! {
    ///     Some(1), OptionType::fmap(0.into(), |x| x + 1);
    ///     Some(true), OptionType::fmap(false.into(), |x| x.not());
    ///     Some(s("abcd")), OptionType::fmap(s("ab").into(), |x| x + "cd");
    /// }
    /// ```
    fn fmap<T, U>(value: Self::Type<T>, f: impl FnMut(T) -> U) -> Self::Type<U> {
        value.map(f)
    }
}

impl Applicative for OptionType {
    /// # Examples
    /// 
    /// ```
    /// use aoko::{assert_eqs, no_std::functions::fam::*};
    /// 
    /// assert_eqs! {
    ///     Some(0), OptionType::pure(0);
    ///     Some(true), OptionType::pure(true);
    ///     Some("xy"), OptionType::pure("xy");
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
    ///     Some(1), OptionType::apply(0.into(), Some(|x| x + 1));
    ///     Some(true), OptionType::apply(false.into(), Some(|x: bool| x.not()));
    ///     Some(s("abcd")), OptionType::apply(s("ab").into(), Some(|x| x + "cd"));
    /// }
    /// ```
    fn apply<T, U>(value: Self::Type<T>, f: Self::Type<impl FnMut(T) -> U>) -> Self::Type<U> {
        value.zip(f).map(|(v, mut f)| f(v))
    }
}

impl Monad for OptionType {
    /// # Examples
    /// 
    /// ```
    /// use std::ops::Not;
    /// use aoko::{assert_eqs, no_std::functions::{fun::s, fam::*}};
    /// 
    /// assert_eqs! {
    ///     Some(1), OptionType::bind(0.into(), |x| Some(x + 1));
    ///     Some(true), OptionType::bind(false.into(), |x| x.not().into());
    ///     Some(s("abcd")), OptionType::bind(s("ab").into(), |x| Some(x + "cd"));
    /// }
    /// ```
    fn bind<T, U>(value: Self::Type<T>, f: impl FnMut(T) -> Self::Type<U>) -> Self::Type<U> {
        value.and_then(f)
    }
}