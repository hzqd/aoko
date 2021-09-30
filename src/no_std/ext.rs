/// This trait is to implement some extension functions,
/// which need a generic return type, for any sized type.
pub trait AnyExt1<R>: Sized {
    /// Performs operation `f` with `&self`, returns the closure result.
    ///
    /// Moves environment variable(s) to closure by default.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::ext::*;
    ///
    /// let s = "Hello".let_ref(|s| format!("String is: {}", s));
    /// assert_eq!(s, "String is: Hello");
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
    /// use aoko::no_std::ext::*;
    ///
    /// let v = vec!["a", "b", "c"]
    ///     .let_mut(|v| { v.push("d"); format!("Vector is: {:?}", v) });
    /// assert_eq!(v, "Vector is: [\"a\", \"b\", \"c\", \"d\"]");
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
    /// use aoko::no_std::ext::*;
    ///
    /// assert_eq!(1, 1.let_owned(|i| i));
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
    /// use aoko::no_std::ext::*;
    ///
    /// let s = "abc".also_ref(|s| s.chars().for_each(|c| print!("{}", c)));
    /// assert_eq!(s, "abc");
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
    /// use aoko::no_std::ext::*;
    ///
    /// let v = vec!["Hello", "Kotlin"].also_mut(|v| v[1] = "Rust");
    /// assert_eq!(v, vec!["Hello", "Rust"]);
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
    /// use aoko::no_std::ext::*;
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
}

impl<T, R> AnyExt1<R> for T {}

/// This trait is to implement some extension functions for any sized type.
pub trait AnyExt: Sized {
    /// Chainable `drop`
    fn drop(self) {}

    /// Returns `Some(self)` if it satisfies the given predicate function,
    /// or `None` if it doesn't.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::ext::*;
    ///
    /// assert_eq!(Some("Hello"), "Hello".take_if(|s| s.starts_with("Hel")));
    /// assert_eq!(None, "Hello".take_if(|s| s.starts_with("Wor")))
    /// ```
    fn take_if(self, f: impl FnOnce(&Self) -> bool) -> Option<Self> {
        if f(&self) { Some(self) } else { None }
    }

    /// Returns `Some(self)` if it doesn't satisfy the given predicate function,
    /// or `None` if it does.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::ext::*;
    ///
    /// assert_eq!(None, "Hello".take_unless(|s| s.starts_with("Hel")));
    /// assert_eq!(Some("Hello"), "Hello".take_unless(|s| s.starts_with("Wor")))
    /// ```
    fn take_unless(self, f: impl FnOnce(&Self) -> bool) -> Option<Self> {
        if !f(&self) { Some(self) } else { None }
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
    /// use aoko::no_std::ext::*;
    ///
    /// let s = "Hello World";
    /// assert_eq!(Some("lo Wo"), s.starts_with("Hel").if_true(&s[3..8]));
    /// assert_eq!(None, s.starts_with("Wor").if_true(&s[3..8]));
    /// ```
    fn if_true(self, value: R) -> Option<R> {
        if self { Some(value) } else { None }
    }

    /// Chainable `if`, returns `Some(value)` when the condition is `false`
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::ext::*;
    ///
    /// let s = "Hello World";
    /// assert_eq!(None, s.starts_with("Hel").if_false(&s[3..8]));
    /// assert_eq!(Some("lo Wo"), s.starts_with("Wor").if_false(&s[3..8]));
    /// ```
    fn if_false(self, value: R) -> Option<R> {
        if !self { Some(value) } else { None }
    }

    /// Returns `Some(f())` if the bool is true, or `None` otherwise
    ///
    /// # Examples
    ///
    /// ```
    /// use aoko::no_std::ext::*;
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
        if !self { Some(f()) } else { None }
    }
}