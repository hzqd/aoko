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
/// asserts!(true; 1 + 1 == 2; "".chars().next().is_none(););
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

/// `Struct::default()`: assigning user-defined values to fields directly.
/// 
/// # Principles
/// 
/// Text replacement, automatic function generation.
/// 
/// # Examples
/// 
/// ``` rust
/// use aoko::{struct_default, assert_eqs};
/// 
/// struct_default!(
///     #[derive(Debug)]
///     pub struct A<'a> {
///         pub  foo: u8 = 123,
///         bar: &'a str = "abc",
///     }
///     struct B {}
///     struct C;
/// );
/// 
/// assert_eqs!(
///     123, A::default().foo;
///     "abc", A::default().bar;
///     "A { foo: 123, bar: \"abc\" }", format!("{:?}", A::default());
/// );
/// ```
#[macro_export]
macro_rules! struct_default {
    ($vis:vis struct $s_name:ident;) => {$vis struct $s_name;};

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
        struct_default! {
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
/// use aoko::{struct_new, assert_eqs};
/// 
/// struct_new!(
///     #[derive(Debug)]
///     pub struct A<'a, T>(foo: T, pub bar: &'a str,) where T: Copy {
///         pub  abc: u8 = 255,
///         xyz: &'a str = "xyz",
///     }
///     struct B {}
///     struct C;
/// );
/// 
/// let test = A::new(123, "bar");
/// 
/// assert_eqs!(
///     123, test.foo;
///     255, test.abc;
///     "bar", test.bar;
///     "xyz", test.xyz;
///     format!("{:?}", test), "A { foo: 123, bar: \"bar\", abc: 255, xyz: \"xyz\" }";
/// );
/// ```
#[macro_export]
macro_rules! struct_new {
    ($vis:vis struct $s_name:ident;) => {$vis struct $s_name;};

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
        struct_new! {
            $($tail)*
        }
    };

    () => {}
}