/// Swaps two variables' value.
/// 
/// # Examples
/// 
/// ```
/// use aoko::swap;
/// 
/// let mut foo = 'a';
/// let mut bar = 'b';
/// swap!(foo, bar);
/// assert_eq!(('b', 'a'), (foo, bar));
/// ```
#[macro_export]
macro_rules! swap {
    ($a:expr, $b:expr) => {
        let t = $a;
        $a = $b;
        $b = t;
    };
}