use crate::no_std::pipelines::{pipe::Pipe, tap::Tap};
use core::{cell::{Cell, RefCell}, ops::{BitXorAssign, Not}, str::Utf8Error};
use alloc::{boxed::Box, format, rc::Rc, str, string::String, sync::Arc, vec::Vec, borrow::Cow};
use itertools::Itertools;
use super::fam::{Applicative, Maybe, Either, Vector};

/// This trait is to implement some extension functions,
/// which need a generic return type, for any sized type.
pub trait AnyExt1<R>: Sized {
    /// The Y Combinator
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// fn factorial(n: u8) -> u8 {
    ///     n.y(|f, n| match n {
    ///         0 => 1,
    ///         n => n * f(n - 1),
    ///     })
    /// }
    /// assert_eq!(factorial(5), 5 * 4 * 3 * 2 * 1);
    ///
    /// fn fibonacci(n: u8) -> u8 {
    ///     n.y(|f, n| match n {
    ///         0 => 0,
    ///         1 => 1,
    ///         n => f(n - 1) + f(n - 2),
    ///     })
    /// }
    /// assert_eq!(fibonacci(10), 55);
    /// ```
    fn y(self, f: impl Copy + Fn(&dyn Fn(Self) -> R, Self) -> R) -> R {
        // The Y Combinator
        fn y<T, R>(f: impl Copy + Fn(&dyn Fn(T) -> R, T) -> R) -> impl Fn(T) -> R {
            move |a| f(&y(f), a)
        }
        // Chainable
        y(f)(self)
    }

    /// Returns `Some(f())` if it satisfies the given predicate function,
    /// or `None` if it doesn't.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!("Hello World".to_string().into_some(), "Hello".if_then(|s| s.starts_with("Hel"), |s| format!("{} World", s)));
    /// assert_eq!(None, "Hello".if_then(|s| s.starts_with("Wor"), |_| ()));
    /// ```
    fn if_then(self, r#if: impl FnOnce(&Self) -> bool, then: impl FnOnce(Self) -> R) -> Option<R> {
        if r#if(&self) { then(self).into_some() } else { None }
    }

    /// Returns `Some(f())` if it doesn't satisfy the given predicate function,
    /// or `None` if it does.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!(None, "Hello".if_not_then(|s| s.starts_with("Hel"), |_| ()));
    /// assert_eq!("Hello World".to_string().into_some(), "Hello".if_not_then(|s| s.starts_with("Wor"), |s| format!("{} World", s)));
    /// ```
    fn if_not_then(self, unless: impl FnOnce(&Self) -> bool, then: impl FnOnce(Self) -> R) -> Option<R> {
        self.if_then(|x| Not::not.compose(unless)(x), then)
    }
}

impl<T, R> AnyExt1<R> for T {}

/// This trait is to implement some extension functions for any sized type.
pub trait AnyExt: Sized {
    /// Chainable `drop`
    fn drop(self) {}

    /// Convert `value` to `Some(value)`
    fn into_some(self) -> Option<Self> {
        self.pipe(Maybe::pure)
    }

    /// Convert `value` to `Ok(value)`
    fn into_ok<B>(self) -> Result<Self, B> {
        self.pipe(Either::pure)
    }

    /// Convert `value` to `Err(value)`
    fn into_err<A>(self) -> Result<A, Self> {
        Result::from(Err(self))
    }

    /// Convert `value` to `Box::new(value)`
    fn into_box(self) -> Box<Self> {
        self.pipe(Box::new)
    }

    /// Convert `value` to `Cell::new(value)`
    fn into_cell(self) -> Cell<Self> {
        self.pipe(Cell::new)
    }

    /// Convert `value` to `RefCell::new(value)`
    fn into_refcell(self) -> RefCell<Self> {
        self.pipe(RefCell::new)
    }

    /// Convert `value` to `Rc::new(value)`
    fn into_rc(self) -> Rc<Self> {
        self.pipe(Rc::new)
    }

    /// Convert `value` to `Rc::new(Cell::new(value))`
    fn into_rc_cell(self) -> Rc<Cell<Self>> {
        Rc::new.compose(Cell::new)(self)
    }

    /// Convert `value` to `Rc::new(RefCell::new(value))`
    fn into_rc_refcell(self) -> Rc<RefCell<Self>> {
        Rc::new.compose(RefCell::new)(self)
    }

    /// Convert `value` to `Arc::new(value)`
    fn into_arc(self) -> Arc<Self> {
        self.pipe(Arc::new)
    }

    /// Consumes `self`,
    /// returns the name of its type as a string slice and the receiver `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!("".type_name(), "&str");
    /// assert_eq!((&"").type_name(), "&&str");
    /// ```
    fn type_name(self) -> &'static str {
        core::any::type_name::<Self>()
    }

    /// Consumes `self`,
    /// returns the size of its type in number and the receiver `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!(().type_size(), 0);
    /// assert_eq!((&()).type_size(), 8);
    /// assert_eq!([(), ()].type_size(), 0);
    /// ```
    fn type_size(self) -> usize {
        core::mem::size_of::<Self>()
    }

    /// Consumes `self`,
    /// returns the name of its type as a string slice and the receiver `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!("".type_name_with_value().0, "&str");
    /// assert_eq!("s".type_name_with_value().1, "s");
    /// assert_eq!((&"").type_name_with_value().0, "&&str");
    /// ```
    fn type_name_with_value(self) -> (&'static str, Self) {
        (core::any::type_name::<Self>(), self)
    }
    
    /// Consumes `self`,
    /// returns the size of its type in number and the receiver `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!(().type_size_with_value().0, 0);
    /// assert_eq!(().type_size_with_value().1, ());
    /// assert_eq!((&()).type_size_with_value().0, 8);
    /// assert_eq!([(), ()].type_size_with_value().0, 0);
    /// ```
    fn type_size_with_value(self) -> (usize, Self) {
        (core::mem::size_of::<Self>(), self)
    }

    /// Returns `Some(self)` if it satisfies the given predicate function,
    /// or `None` if it doesn't.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!(Some("Hello"), "Hello".if_take(|s| s.starts_with("Hel")));
    /// assert_eq!(None, "Hello".if_take(|s| s.starts_with("Wor")));
    /// ```
    fn if_take(self, f: impl FnOnce(&Self) -> bool) -> Option<Self> {
        self.if_not_then(|x| Not::not.compose(f)(x), |s| s)
    }

    /// Returns `Some(self)` if it doesn't satisfy the given predicate function,
    /// or `None` if it does.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!(None, "Hello".if_not_take(|s| s.starts_with("Hel")));
    /// assert_eq!(Some("Hello"), "Hello".if_not_take(|s| s.starts_with("Wor")));
    /// ```
    fn if_not_take(self, f: impl FnOnce(&Self) -> bool) -> Option<Self> {
        self.if_take(|x| Not::not.compose(f)(x))
    }
}

impl<T> AnyExt for T {}

/// This trait is to implement some extension functions for `bool` type.
pub trait BoolExt<R> {
    fn if_true(self, value: R) -> Option<R>;
    fn if_false(self, value: R) -> Option<R>;
    fn then_false(self, f: impl FnOnce() -> R) -> Option<R>;
}

impl<R> BoolExt<R> for bool {
    /// Chainable `if`, returns `Some(value)` when the condition is `true`
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// let s = "Hello World";
    /// assert_eq!(Some("lo Wo"), s.starts_with("Hel").if_true(&s[3..8]));
    /// assert_eq!(None, s.starts_with("Wor").if_true(&s[3..8]));
    /// ```
    fn if_true(self, value: R) -> Option<R> {
        self.if_not_then(|s| s.not(), |_| value)
    }

    /// Chainable `if`, returns `Some(value)` when the condition is `false`
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// let s = "Hello World";
    /// assert_eq!(None, s.starts_with("Hel").if_false(&s[3..8]));
    /// assert_eq!(Some("lo Wo"), s.starts_with("Wor").if_false(&s[3..8]));
    /// ```
    fn if_false(self, value: R) -> Option<R> {
        self.if_not_then(|s| *s, |_| value)
    }

    /// Returns `Some(f())` if the receiver is `false`, or `None` otherwise
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// let s = "Hello World";
    ///
    /// // then:
    /// assert_eq!(Some("lo Wo"), s.starts_with("Hel").then(|| &s[3..8]));
    /// assert_eq!(None, s.starts_with("Wor").then(|| &s[3..8]));
    ///
    /// // then_false:
    /// assert_eq!(None, s.starts_with("Hel").then_false(|| &s[3..8]));
    /// assert_eq!(Some("lo Wo"), s.starts_with("Wor").then_false(|| &s[3..8]));
    /// ```
    fn then_false(self, f: impl FnOnce() -> R) -> Option<R> {
        self.if_not_then(|s| *s, |_| f())
    }
}

/// This trait is to implement some extension functions for `[T]` type.
pub trait ArrExt {
    fn swap_xor(self, i: usize, j: usize) -> Self;
}

impl<T> ArrExt for &mut [T] where T: BitXorAssign<T> + Copy {
    /// Swaps two elements in a slice.
    ///
    /// # Parameters
    ///
    /// * i - The index of the first element
    /// * j - The index of the second element
    ///
    /// # Panics
    ///
    /// Panics if `i` or `j` are out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    /// 
    /// let mut v = [0, 1, 2, 3, 4];
    /// v.swap_xor(1, 3);
    /// assert!(v == [0, 3, 2, 1, 4]);
    /// ```
    /// 
    /// # Principles
    /// 
    /// * a = 甲, b = 乙
    /// 
    /// * a = a ^ b    =>    a = 甲 ^ 乙, b = 乙
    /// * b = a ^ b    =>    a = 甲 ^ 乙, b = 甲 ^ (乙 ^ 乙) = 甲 ^ 0 = 甲
    /// * a = a ^ b    =>    a = 甲 ^ 乙 ^ 甲 = 甲 ^ 甲 ^ 乙 = 0 ^ 乙 = 乙
    fn swap_xor(self, i: usize, j: usize) -> Self {
        self.tap_mut(|s| if i != j {
            s[i] ^= s[j];
            s[j] ^= s[i];
            s[i] ^= s[j];
        })
    }
}

pub trait StrExt {
    fn split_not_empty_and_join(self, split: &str, join: &str) -> String;
    fn wildcard_match(self, pattern_text: &str) -> bool;
}

impl StrExt for &str {
    fn split_not_empty_and_join(self, split: &str, join: &str) -> String {
        self.split(split).filter(|s| s.bytes().next().is_some()).join(join)
    }

    /// https://gist.github.com/mo-xiaoming/9fb87da16d6ef459e1b94c16055b9978
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std::ops::Not;
    /// use aoko::{asserts, no_std::functions::ext::*};
    /// 
    /// asserts! {
    ///     "abc".wildcard_match("abc");
    ///     "a0c".wildcard_match("abc*").not();
    ///     "mississippi".wildcard_match("mississipp**");
    ///     "mississippi".wildcard_match("mississippi*");
    ///     "mississippi.river".wildcard_match("*.*");
    ///     "mississippi.river".wildcard_match("*ip*");
    ///     "mississippi.river".wildcard_match("m*i*.*r");
    ///     "mississippi.river".wildcard_match("m*x*.*r").not();
    /// }
    /// ```
    fn wildcard_match(self, pattern: &str) -> bool {
        struct AfterWildcard {
            plain_idx: usize,
            pattern_idx: usize,
        }
        // it is None if there are no prev wildcard
        // if there were, then `plain_idx` stores *next* index in plain text that wildcard supposes to match
        //                     `pattern_idx` stores *next* index right after the wildcard
        //                     when they first assigned
        //                     latter they become to be the next possible non matches
        //                     anything pre these two considered match
        let mut after_wildcard: Option<AfterWildcard> = None;

        // current indices moving in two strings
        let mut cur_pos_plain_text = 0_usize;
        let mut cur_pos_pattern_text = 0_usize;

        loop {
            // current chars in two strings
            let plain_c = self.chars().nth(cur_pos_plain_text);
            let pattern_c = pattern.chars().nth(cur_pos_pattern_text);

            if plain_c.is_none() {
                // plain text ends
                match pattern_c {
                    None => return true, // pattern text ends as well, happy ending
                    Some('*') => // since we make wildcard matches non-eager
                                // go back to use `after_wildcard` only make it less possible to match
                        // matches if pattern only have '*' till the end
                        return pattern[cur_pos_pattern_text..].chars().all(|e| e == '*'),

                    Some(w) => {
                        // go back to last wildcard and try next possible char in plain text
                        let Some(AfterWildcard { ref mut plain_idx, pattern_idx }) = after_wildcard else {
                            // if no prev wildcard exists, then that's it, no match
                            return false;
                        };
                        // move `plain_idx` in `after_wildcard` to the next position of `w` in plain text
                        // any positions before that is impossible to match the pattern text
                        let Some(i) = self[*plain_idx..].chars().position(|c| c == w) else {
                            // if `w` doesn't even exists in plain text, then give up
                            return false;
                        };
                        *plain_idx = i;
                        cur_pos_plain_text = *plain_idx;
                        cur_pos_pattern_text = pattern_idx;
                        continue;
                    }
                }
            } else if plain_c != pattern_c {
                if pattern_c == Some('*') {
                    // skip '*'s, one is as good as many
                    let Some(i) = pattern[cur_pos_pattern_text..].chars().position(|e| e != '*') else {
                        // even better, pattern text ends with a '*', which matches everything
                        return true;
                    };
                    cur_pos_pattern_text += i;

                    // pattern text doesn't end with this '*', then find next non '*' char
                    let w = pattern.chars().nth(cur_pos_pattern_text).unwrap();
                    // char in pattern text does exist in plain text
                    let Some(i) = self[cur_pos_plain_text..].chars().position(|c| c == w) else {
                        // otherwise, we cannot match
                        return false;
                    };
                    // update both positions
                    after_wildcard.replace(AfterWildcard {
                        plain_idx: i,
                        pattern_idx: cur_pos_pattern_text,
                    });
                    continue;
                }
                let Some(AfterWildcard { pattern_idx, .. }) = after_wildcard else {
                    return false;
                };
                // go back to last wildcard
                if pattern_idx != cur_pos_pattern_text {
                    cur_pos_pattern_text = pattern_idx;
                    // matches this char, move pattern idx forward
                    if pattern.chars().nth(cur_pos_pattern_text) == plain_c {
                        cur_pos_pattern_text += 1;
                    }
                }
                // try next plain text char anyway, current one gets swallowed by '*'
                // or by a matching char in pattern text
                cur_pos_plain_text += 1;
                continue;
            } else {
                cur_pos_plain_text += 1;
                cur_pos_pattern_text += 1;
            }
        }
    }
}

/// This trait is to implement some extension functions for `&[u8]` and `Vec<u8>` type.
pub trait Utf8Ext {
    fn to_str(&self) -> Result<&str, Utf8Error>;
    fn to_str_lossy(&self) -> Cow<str>;
}

impl Utf8Ext for [u8] {
    /// Converts a slice of bytes to a string slice.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use aoko::no_std::functions::ext::*;
    /// 
    /// assert_eq!("💖", [240, 159, 146, 150].to_str().unwrap());
    /// ```
    fn to_str(&self) -> Result<&str, Utf8Error> {
        str::from_utf8(self)
    }

    /// Converts a slice of bytes to a string, including invalid characters.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use aoko::{assert_eqs, no_std::functions::ext::*};
    /// 
    /// assert_eqs! {
    ///     "💖", [240, 159, 146, 150].to_str_lossy();
    ///     "Hello �World", b"Hello \xF0\x90\x80World".to_str_lossy();
    /// }
    /// 
    /// ```
    fn to_str_lossy(&self) -> Cow<str> {
        String::from_utf8_lossy(self)
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
    /// use aoko::no_std::functions::ext::*;
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

/// This trait is to implement some extension functions for `Option<T>` type.
pub trait OptionExt<T> {
    fn or_else_some(self, f: impl FnOnce() -> T) -> Self;
    fn apply<R>(self, f: Option<impl FnMut(T) -> R>) -> Option<R>;
}

impl<T> OptionExt<T> for Option<T> {
    /// This function is similar to `or_else`,
    /// but convert closure result to `Some` automatically.
    /// 
    /// # Examples
    /// 
    /// ``` rust
    /// use aoko::no_std::functions::ext::*;
    /// 
    /// assert_eq!(Some(0), None::<u8>.or_else_some(|| 0));
    /// ```
    fn or_else_some(self, f: impl FnOnce() -> T) -> Self {
        match self {
            Some(_) => self,
            None => f().into_some()
        }
    }

    /// # Examples
    /// 
    /// ```
    /// use std::ops::Not;
    /// use aoko::{assert_eqs, no_std::functions::{fun::s, ext::*}};
    /// 
    /// assert_eqs! {
    ///     Some(1),         Some(0).apply(Some(|x| x + 1));
    ///     Some(true),      Some(false).apply(Some(|x: bool| x.not()));
    ///     Some(s("abcd")), Some(s("ab")).apply(Some(|x| x + "cd"));
    /// }
    /// ```
    fn apply<R>(self, f: Option<impl FnMut(T) -> R>) -> Option<R> {
        Maybe::apply(self, f)
    }
}

/// This trait is to implement some extension functions for `Result<T, E>` type.
pub trait ResultExt<T, E> {
    fn zip<U>(self, other: Result<U, E>) -> Result<(T, U), E>;
    fn apply<U>(self, f: Result<impl FnMut(T) -> U, E>) -> Result<U, E>;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    /// Zips `self` with another `Result`.
    ///
    /// If `self` is `Ok(s)` and `other` is `Ok(o)`, this method returns `Ok((s, o))`.
    /// Otherwise, `Err` is returned.
    /// 
    /// # Examples
    ///
    /// ```
    /// use aoko::{assert_eqs, no_std::functions::ext::*};
    /// 
    /// let x = Ok(1);
    /// let y = Ok("hi");
    /// let z = Err::<u8, _>(());
    ///
    /// assert_eqs! {
    ///     x.zip(y), Ok((1, "hi"));
    ///     x.zip(z), Err(());
    /// }
    /// ```
    fn zip<U>(self, other: Result<U, E>) -> Result<(T, U), E> {
        match (self, other) {
            (Ok(a), Ok(b)) => (a, b).into_ok(),
            (Err(e), _) | (_, Err(e)) => e.into_err(),
        }
    }

    /// # Examples
    /// 
    /// ```
    /// use std::ops::Not;
    /// use aoko::{assert_eqs, no_std::functions::{fun::s, ext::*}};
    /// 
    /// let mut f = Ok(|x| x + "cd");
    /// f = Err(());
    /// 
    /// assert_eqs! {
    ///     Ok::<_, ()>(0), Ok(0).apply(Ok(|x| x / 1));
    ///     Err(-1),        Err(-1).apply(Ok(|x: bool| x.not()));
    ///     Err(()),        Ok(s("ab")).apply(f);
    /// }
    /// ```
    fn apply<U>(self, f: Result<impl FnMut(T) -> U, E>) -> Result<U, E> {
        Either::apply(self, f)
    }
}

pub trait VecExt<T> {
    fn apply<U>(self, f: Vec<impl FnMut(T) -> U>) -> Vec<U>;
}

impl<T> VecExt<T> for Vec<T> {
    /// Applies the function to the element.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use aoko::no_std::functions::ext::*;
    /// 
    /// let v = vec![2, 4, 6];
    /// let f = Vec::from([|x| x + 1, |y| y * 2, |z| z / 3]);
    /// 
    /// assert_eq!(v.apply(f), vec![3, 8, 2]);
    /// ```
    fn apply<U>(self, f: Vec<impl FnMut(T) -> U>) -> Vec<U> {
        Vector::apply(self, f)
    }
}

/// This trait is to implement some extension functions with currying two parameters.
pub trait Curry<'a, P1, P2, R> {
    fn curryl(self) -> impl FnOnce(P1) -> Box<dyn FnOnce(P2) -> R + 'a>;
    fn curryr(self) -> impl FnOnce(P2) -> Box<dyn FnOnce(P1) -> R + 'a>;
}

impl<'a, P1: 'a, P2: 'a, R, F> Curry<'a, P1, P2, R> for F where F: FnOnce(P1, P2) -> R + 'a {
    /// Two parameters, currying from left to right.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// fn sub(a: u8, b: u8) -> u8 { a - b }
    /// let c1 = sub.curryl();
    /// assert_eq!(c1(3)(2), 1);
    /// ```
    fn curryl(self) -> impl FnOnce(P1) -> Box<dyn FnOnce(P2) -> R + 'a> {
        |p1| (|p2| self(p1, p2)).into_box()
    }

    /// Two parameters, currying from right to left.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// fn sub(a: u8, b: u8) -> u8 { a - b }
    /// let cu = sub.curryr(); 
    /// assert_eq!(cu(2)(3), 1);
    /// ```
    fn curryr(self) -> impl FnOnce(P2) -> Box<dyn FnOnce(P1) -> R + 'a> {
        |p2| (|p1| self(p1, p2)).into_box()
    }
}

/// This trait is to implement some extension functions whose type is `FnOnce`.
pub trait FnOnceExt<T, U, R> {
    fn combine(self, g: impl FnOnce(U) -> R) -> impl FnOnce(T) -> R;
    fn compose(self, g: impl FnOnce(R) -> T) -> impl FnOnce(R) -> U;
}

impl<T, U, R, F> FnOnceExt<T, U, R> for F where F: FnOnce(T) -> U {
    /// Combining two functions.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::{ext::*, fun::s};
    ///
    /// fn inc(arr: &[u8]) -> Vec<u8> { arr.iter().map(|byte| byte + 1).collect() }
    /// fn sum(v: Vec<u8>) -> u8 { v.iter().sum() }
    /// fn to_string(x: u8) -> String { x.to_string() }
    /// 
    /// let func = inc.combine(sum).combine(to_string);
    /// assert_eq!(s("45"), func(&[0, 1, 2, 3, 4, 5, 6, 7, 8]));
    /// ```
    fn combine(self, g: impl FnOnce(U) -> R) -> impl FnOnce(T) -> R {
        |x| x.pipe(self).pipe(g)  // |x| g(self(x))
    }

    /// Combining two functions in reverse order.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::{ext::*, fun::s};
    ///
    /// fn inc(arr: &[u8]) -> Vec<u8> { arr.iter().map(|byte| byte + 1).collect() }
    /// fn sum(v: Vec<u8>) -> u8 { v.iter().sum() }
    /// fn to_string(x: u8) -> String { x.to_string() }
    /// 
    /// let func = to_string.compose(sum).compose(inc);
    /// assert_eq!(s("45"), func(&[0, 1, 2, 3, 4, 5, 6, 7, 8]));
    /// ```
    fn compose(self, g: impl FnOnce(R) -> T) -> impl FnOnce(R) -> U {
        g.combine(self)  // |x| self(g(x))
    }
}