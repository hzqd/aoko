/// Abbr. of `let mut`
/// 
/// # Examples
/// 
/// ```
/// use aoko::lm;
/// 
/// lm!(foo = 1024);
/// foo = 2048;
/// assert_eq!(2048, foo);
/// ```
#[macro_export]
macro_rules! lm {
    ($a:ident = $b:expr) => {
        let mut $a = $b;
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
/// let (foo, bar) = ('a', 'b');
/// swap!(foo, bar);
/// assert_eq!(('b', 'a'), (foo, bar));
/// ```
#[macro_export]
macro_rules! swap {
    ($a:ident, $b:ident) => {
        let ($b, $a) = ($a, $b);
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
/// let (foo, bar) = ('a', 'b');
/// swap_mut!(foo, bar);
/// assert_eq!(('b', 'a'), (foo, bar));
/// 
/// foo = 'x';
/// bar = 'y';
/// assert_eq!(('x', 'y'), (foo, bar));
/// ```
#[macro_export]
macro_rules! swap_mut {
    ($a:ident, $b:ident) => {
        let (mut $b, mut $a) = ($a, $b);
    };
}