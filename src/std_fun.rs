use std::io::stdin;
use super::std_ext::KtStd;

/// Reads a line of input from the standard input stream.
///
/// Returns a `Some` value when content is not empty.
///
/// # Examples
///
/// ```no_run
/// use aoko::std_fun::*;
/// 
/// // If you ensure the input is not empty, or want to panic if it is empty, use:
/// read_line().unwrap();
///
/// // If you want to return a default value when the input is empty, use:
/// read_line().unwrap_or(String::from("default_value"));
///
/// // If you just want empty value is "", use:
/// read_line().unwrap_or_default();
/// ```
pub fn read_line() -> Option<String> {
    String::new().also_mut(|s| stdin().read_line(s))
        .trim_end().to_string()
        .let_owned(|s| if s.len() > 0 { Some(s) } else { None })
}

/// Breaks loop when command line input is empty. (Press `Enter` to exit.)
///
/// Usually used in command line program as `.exe` file on Windows to prevent it from exiting directly.
pub fn wait_enter() {
    while read_line() != None {}
}

/// The Y Combinator
///
/// # Examples
///
/// ```
/// use aoko::std_fun::*;
///
/// fn fact(n: usize) -> usize {
///     y(|f, n| match n {
///         0 | 1 => 1,
///         n => n * f(n - 1),
///     })(n)
/// }
/// assert_eq!(fact(5), 5 * 4 * 3 * 2 * 1);
///
/// fn fibonacci(n: usize) -> usize {
///     y(|f, n| match n {
///         0 => 0,
///         1 => 1,
///         n => f(n - 1) + f(n - 2),
///     })(n)
/// }
/// assert_eq!(fibonacci(10), 55);
/// ```
pub fn y<T, R>(f: impl Copy + Fn(&dyn Fn(T) -> R, T) -> R) -> impl Fn(T) -> R {
    move |a| f(&y(f), a)
}