/// Abbr. of `let`
/// 
/// # Examples
/// 
/// ```
/// use aoko::l;
/// 
/// l!(foo = 233; bar: u16 = 666;);
/// assert_eq!((233, 666), (foo, bar));
/// ```
#[macro_export]
macro_rules! l {
    ($($a:ident $(:$t:ty)? = $b:expr);* $(;)?) => {
        $(let $a $(:$t)? = $b;)*
    };
}

/// Abbr. of `let mut`
/// 
/// # Examples
/// 
/// ```
/// use aoko::lm;
/// 
/// lm!(foo = 233; bar: u16 = 1024;);
/// foo = 666; bar = 2048;
/// assert_eq!((666, 2048), (foo, bar));
/// ```
#[macro_export]
macro_rules! lm {
    ($($a:ident $(:$t:ty)? = $b:expr);* $(;)?) => {
        $(let mut $a $(:$t)? = $b;)*
    };
}

/// Conveniently create String variables.
/// 
/// # Examples
/// 
/// ```
/// use aoko::{s, no_std::functions::fun::s};
/// 
/// s!(a = "a"; b = "b"; c = "c";);
/// assert_eq!((a, b, c), (s("a"), s("b"), s("c")));
/// ```
#[macro_export]
macro_rules! s {
    ($($a:ident = $b:expr);* $(;)?) => {
        $(let $a = aoko::no_std::functions::fun::s($b);)*
    };
}

/// Conveniently create mutable String variables.
/// 
/// # Examples
/// 
/// ```
/// use aoko::{sm, no_std::functions::fun::s};
/// 
/// sm!(a = "a"; b = "b"; c = "c";);
/// assert_eq!((a, b, c), (s("a"), s("b"), s("c")));
/// 
/// a = s("x"); b = s("y"); c = s("z");
/// assert_eq!((a, b, c), (s("x"), s("y"), s("z")));
/// ```
#[macro_export]
macro_rules! sm {
    ($($a:ident = $b:expr);* $(;)?) => {
        $(let mut $a = aoko::no_std::functions::fun::s($b);)*
    };
}

/// Swaps two variables' value.
/// 
/// # Principles
/// 
/// Shadowing by two immutable variables.
/// 
/// # Examples
/// 
/// ```
/// use aoko::swap;
/// 
/// let (a, b, c, d) = (1, 2, 3, 4);
/// swap!(a, b; c, d;);
/// assert_eq!((a, b, c, d), (2, 1, 4, 3));
/// ```
#[macro_export]
macro_rules! swap {
    ($($a:ident, $b:ident);* $(;)?) => {
        $(let ($b, $a) = ($a, $b);)*
    };
}

/// Swaps two variables' value.
/// 
/// # Principles
/// 
/// Shadowing by two mutable variables.
/// 
/// # Examples
/// 
/// ```
/// use aoko::swap_mut;
/// 
/// let (a, b, c, d) = (1, 2, 3, 4);
/// swap_mut!(a, b; c, d;);
/// assert_eq!((a, b, c, d), (2, 1, 4, 3));
/// 
/// a = 10; b = 20; c = 30; d = 40;
/// assert_eq!((a, b, c, d), (10, 20, 30, 40));
/// ```
#[macro_export]
macro_rules! swap_mut {
    ($($a:ident, $b:ident);* $(;)?) => {
        $(let (mut $b, mut $a) = ($a, $b);)*
    };
}

/// Assert multiple expressions.
///
/// # Principles
/// 
/// Loop `assert!` statements.
/// 
/// # Examples
/// 
/// ```
/// use aoko::asserts;
/// 
/// asserts!(true; 1 + 1 == 2; "".bytes().next().is_none(););
/// ```
#[macro_export]
macro_rules! asserts {
    ($($a:expr);* $(;)?) => {
        $(assert!($a);)*
    };
}

/// Assert multiple eq expressions.
///
/// # Principles
/// 
/// Loop `assert_eq!` statements.
/// 
/// # Examples
/// 
/// ```
/// use aoko::assert_eqs;
/// 
/// assert_eqs!(0, 0; "", ""; 'z', 'z'; true, true;);
/// ```
#[macro_export]
macro_rules! assert_eqs {
    ($($a:expr, $b:expr);* $(;)?) => {
        $(assert_eq!($a, $b);)*
    };
}

/// Assert multiple not eq expressions.
///
/// # Principles
/// 
/// Loop `assert_ne!` statements.
/// 
/// # Examples
/// 
/// ```
/// use aoko::assert_nes;
/// 
/// assert_nes!(1, 2; "a", "b"; 'x', 'y'; true, false;);
/// ```
#[macro_export]
macro_rules! assert_nes {
    ($($a:expr, $b:expr);* $(;)?) => {
        $(assert_ne!($a, $b);)*
    };
}

/// An alternative to if expression.
/// 
/// # Examples
/// 
/// ``` rust
/// use aoko::{when, assert_eqs};
/// 
/// assert_eqs! {
///     0, when!(true  => 0 ; 1);
///     1, when!(false => 0 ; 1);
/// };
/// 
/// // Multiple expressions can't return,
/// // generally used to perform operations.
/// # fn op1() {}
/// # let op2 = || ();
/// # fn op3(a: u8) -> u8 { a + a }
/// # let op4 = |a: u8| a * a;
/// when! {
///     true => op1() ; op2(),
///     false => {
///         op1();
///         op3(1)
///     } ; {
///         op2();
///         op4(1)
///     },
///     let a = true => "foo" ; "bar",
///     let b: (u8, u128) = false => (0,1) ; (2,3),
/// };
/// assert_eqs! {
///     a, "foo";
///     b, (2, 3);
/// };
/// ```
#[macro_export]
macro_rules! when {
    ($predicate:expr => $true:expr ; $false:expr) => {
        if $predicate { $true } else { $false }
    };
    ($($(let $a:ident $(:$t:ty)? =)? $predicate:expr => $true:expr ; $false:expr),* $(,)?) => {
        $($(let $a $(:$t)? =)? if $predicate { $true } else { $false };)*
    };
}

/// `Struct::default()`: assigning user-defined values to fields directly.
/// 
/// # Principles
/// 
/// Text replacement, automatic function generation.
/// 
/// # Examples
/// 
/// ``` rust
/// use aoko::{structs_default_decl, assert_eqs};
/// 
/// structs_default_decl!(
///     #[derive(Debug)]
///     pub struct A<'a> {
///         foo: u8 = 233,
///         pub bar: &'a str = "abc",
///     }
///     struct B {}
///     struct C;
/// );
/// 
/// let a = A::default();
/// 
/// assert_eqs!(
///     233, a.foo;
///     "abc", a.bar;
///     "A { foo: 233, bar: \"abc\" }", format!("{:?}", a);
/// );
/// ```
#[macro_export]
macro_rules! structs_default_decl {
    ($vis:vis struct $s_name:ident; $($tail:tt)*) => {$vis struct $s_name; structs_default_decl! { $($tail)* }};

    ($(#[$attr:meta])* $vis:vis struct $name:ident $(<$($generic:tt),*>)? {
        $($field_vis:vis $field:ident: $type:ty = $val:expr),* $(,)?
    }
    $($tail:tt)*) => {
        $(#[$attr])*
        $vis struct $name $(<$($generic),*>)? {
            $($field_vis $field: $type),*
        }
        impl $(<$($generic),*>)? Default for $name $(<$($generic),*>)? {
            fn default() -> Self {
                $name {
                    $($field: $val),*
                }
            }
        }
        structs_default_decl! {
            $($tail)*
        }
    };

    () => {}
}

/// `Struct::new(...)`: define parameters and assigning user-defined values to fields directly.
/// 
/// # Principles
/// 
/// Text replacement, automatic function generation.
/// 
/// # Examples
/// 
/// ``` rust
/// use aoko::{structs_new_decl, assert_eqs};
/// 
/// structs_new_decl!(
///     #[derive(Debug)]
///     pub struct A<'a, T>(pub foo: T,) where T: Copy, T: Ord {
///         pub bar: &'a str = "bar",
///     }
///     struct B {}
///     struct C;
/// );
/// 
/// let a = A::new("foo");
/// 
/// assert_eqs!(
///     "foo", a.foo;
///     "bar", a.bar;
///     "A { foo: \"foo\", bar: \"bar\" }", format!("{:?}", a);
/// );
/// ```
#[macro_export]
macro_rules! structs_new_decl {
    ($vis:vis struct $s_name:ident; $($tail:tt)*) => {$vis struct $s_name; structs_new_decl! { $($tail)* }};

    ($(#[$attr:meta])* $vis:vis struct $s_name:ident $(<$($generic:tt),*>)? $(($($p_vis:vis $p_name:ident: $p_type:ty),* $(,)?))? $(where $($id:tt: $limit:tt),*)? {
        $($field_vis:vis $field:ident: $type:ty = $val:expr),* $(,)?
    }
    $($tail:tt)*) => {
        $(#[$attr])*
        $vis struct $s_name $(<$($generic),*>)? $(where $($id: $limit),*)? {
            $($($p_vis $p_name: $p_type,)*)?
            $($field_vis $field: $type),*
        }
        impl $(<$($generic),*>)? $s_name $(<$($generic),*>)? $(where $($id: $limit),*)? {
            fn new($($($p_name: $p_type),*)?) -> Self {
                $s_name {
                    $($($p_name,)*)?
                    $($field: $val),*
                }
            }
        }
        structs_new_decl! {
            $($tail)*
        }
    };

    () => {}
}

/// `Struct::from()`: assigning user-defined values to fields directly.
/// 
/// # Principles
/// 
/// Text replacement, automatic function generation.
/// 
/// # Examples
/// 
/// ``` rust
/// use aoko::{structs_from_decl, assert_eqs};
/// use std::fmt::Display;
/// 
/// structs_from_decl!(
///     #[derive(Debug, Clone)]
///     pub struct A<T>(from: Option<T>) where T: Display {
///         pub foo: T = from.unwrap(),
///     }
///     struct B {}
///     struct C;
/// );
/// 
/// let a = A::from(Some(233));
/// 
/// assert_eqs!(
///     233, a.foo;
/// );
/// ```
#[macro_export]
macro_rules! structs_from_decl {
    ($vis:vis struct $s_name:ident; $($tail:tt)*) => {$vis struct $s_name; structs_from_decl! { $($tail)* }};

    ($vis:vis struct $s_name:ident {} $($tail:tt)*) => {$vis struct $s_name {} structs_from_decl! { $($tail)* }};

    ($(#[$attr:meta])* $vis:vis struct $name:ident $(<$($generic:tt),*>)? ($from:ident: $from_type:ty) $(where $($id:tt: $limit:tt),*)? {
        $($field_vis:vis $field:ident: $type:ty = $val:expr),* $(,)?
    }
    $($tail:tt)*) => {
        $(#[$attr])*
        $vis struct $name $(<$($generic),*>)? $(where $($id: $limit),*)? {
            $($field_vis $field: $type),*
        }
        impl $(<$($generic),*>)? From<$from_type> for $name $(<$($generic),*>)? $(where $($id: $limit),*)? {
            fn from($from: $from_type) -> Self {
                $name {
                    $($field: $val),*
                }
            }
        }
        structs_from_decl! {
            $($tail)*
        }
    };

    () => {}
}