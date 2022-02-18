use crate::no_std::pipeline::tap::Tap;
use core::{cell::{Cell, RefCell}, ops::BitXorAssign, str::Utf8Error};
use alloc::{boxed::Box, format, rc::Rc, str, string::String, sync::Arc};

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
    /// assert_eq!("Hello World".to_string().into_some(), "Hello".then_if(|s| s.starts_with("Hel"), |s| format!("{} World", s)));
    /// assert_eq!(None, "Hello".then_if(|s| s.starts_with("Wor"), |_| ()));
    /// ```
    fn then_if(self, f1: impl FnOnce(&Self) -> bool, f2: impl FnOnce(Self) -> R) -> Option<R> {
        if f1(&self) { f2(self).into_some() } else { None }
    }

    /// Returns `Some(f())` if it doesn't satisfy the given predicate function,
    /// or `None` if it does.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!(None, "Hello".then_unless(|s| s.starts_with("Hel"), |_| ()));
    /// assert_eq!("Hello World".to_string().into_some(), "Hello".then_unless(|s| s.starts_with("Wor"), |s| format!("{} World", s)));
    /// ```
    fn then_unless(self, f1: impl FnOnce(&Self) -> bool, f2: impl FnOnce(Self) -> R) -> Option<R> {
        if !f1(&self) { f2(self).into_some() } else { None }
    }
}

impl<T, R> AnyExt1<R> for T {}

/// This trait is to implement some extension functions for any sized type.
pub trait AnyExt: Sized {
    /// Chainable `drop`
    fn drop(self) {}

    /// Convert `value` to `Some(value)`
    fn into_some(self) -> Option<Self> {
        self.into()
    }

    /// Convert `value` to `Ok(value)`
    fn into_ok<B>(self) -> Result<Self, B> {
        Ok(self)
    }

    /// Convert `value` to `Err(value)`
    fn into_err<A>(self) -> Result<A, Self> {
        Err(self)
    }

    /// Convert `value` to `Box::new(value)`
    fn into_box(self) -> Box<Self> {
        Box::new(self)
    }

    /// Convert `value` to `Cell::new(value)`
    fn into_cell(self) -> Cell<Self> {
        Cell::new(self)
    }

    /// Convert `value` to `RefCell::new(value)`
    fn into_ref_cell(self) -> RefCell<Self> {
        RefCell::new(self)
    }

    /// Convert `value` to `Rc::new(value)`
    fn into_rc(self) -> Rc<Self> {
        Rc::new(self)
    }

    /// Convert `value` to `Arc::new(value)`
    fn into_arc(self) -> Arc<Self> {
        Arc::new(self)
    }

    /// Consumes `self`,
    /// returns the name of a type as a string slice and the `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!("".type_name().0, "&str");
    /// assert_eq!("s".type_name().1, "s");
    /// assert_eq!((&"").type_name().0, "&&str");
    /// ```
    fn type_name(self) -> (&'static str, Self) {
        (core::any::type_name::<Self>(), self)
    }
    
    /// Consumes `self`,
    /// returns the size of a type in bytes and the `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!(().type_size().0, 0);
    /// assert_eq!(().type_size().1, ());
    /// assert_eq!((&()).type_size().0, 8);
    /// assert_eq!([(), ()].type_size().0, 0);
    /// ```
    fn type_size(self) -> (usize, Self) {
        (core::mem::size_of::<Self>(), self)
    }
    
    /// Returns the name of a type as a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!(String::new().type_ref_name(), "&alloc::string::String");     // auto ref, auto deref.
    /// assert_eq!((&String::new()).type_ref_name(), "&alloc::string::String");  // auto deref.
    /// assert_eq!((&&String::new()).type_ref_name(), "&&alloc::string::String");
    /// ```
    fn type_ref_name(&self) -> &str {
        core::any::type_name::<&Self>()
    }
    
    /// Returns the size of a type in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!(().type_ref_size(), 0);      // auto ref, auto deref.
    /// assert_eq!((&()).type_ref_size(), 0);   // auto deref.
    /// assert_eq!((&&()).type_ref_size(), 8);
    /// ```
    fn type_ref_size(&self) -> usize {
        core::mem::size_of::<Self>()
    }

    /// Returns `Some(self)` if it satisfies the given predicate function,
    /// or `None` if it doesn't.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!(Some("Hello"), "Hello".take_if(|s| s.starts_with("Hel")));
    /// assert_eq!(None, "Hello".take_if(|s| s.starts_with("Wor")));
    /// ```
    fn take_if(self, f: impl FnOnce(&Self) -> bool) -> Option<Self> {
        if f(&self) { self.into_some() } else { None }
    }

    /// Returns `Some(self)` if it doesn't satisfy the given predicate function,
    /// or `None` if it does.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::functions::ext::*;
    ///
    /// assert_eq!(None, "Hello".take_unless(|s| s.starts_with("Hel")));
    /// assert_eq!(Some("Hello"), "Hello".take_unless(|s| s.starts_with("Wor")));
    /// ```
    fn take_unless(self, f: impl FnOnce(&Self) -> bool) -> Option<Self> {
        if !f(&self) { self.into_some() } else { None }
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
        if self { value.into_some() } else { None }
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
        if !self { value.into_some() } else { None }
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
        if !self { f().into_some() } else { None }
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
    /// let mut v = [0, 1, 2, 3, 4];
    /// v.swap(1, 3);
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

/// This trait is to implement some extension functions for `&[u8]` and `Vec<u8>` type.
pub trait Utf8Ext<'a> {
    fn to_str(self) -> Result<&'a str, Utf8Error>;
}

impl<'a> Utf8Ext<'a> for &'a [u8] {
    /// Converts a slice of bytes to a string slice.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use aoko::no_std::functions::ext::*;
    /// 
    /// assert_eq!("💖", [240, 159, 146, 150].to_str().unwrap());
    /// ```
    fn to_str(self) -> Result<&'a str, Utf8Error> {
        str::from_utf8(self)
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
    /// use aoko::no_std::functions::ext::*;
    ///
    /// fn foo(a: u8, b: u8) -> u8 { a - b }
    /// assert_eq!(foo.partial2(2)(3), 1);
    /// ```
    fn partial2(self, p2: P2) -> Box<dyn FnOnce(P1) -> R> {
        (move |p1| self(p1, p2)).into_box()
    }
}