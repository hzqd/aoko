use std::io::stdin;
use super::std_ext::KtStd;

pub fn read_line() -> String {
    String::new().also_mut(|s| stdin().read_line(s))
}

pub fn wait_enter() {
    while read_line().trim() != "" {}
}

pub fn y<T, R>(f: impl Copy + Fn(&dyn Fn(T) -> R, T) -> R) -> impl Fn(T) -> R {
    move |a| f(&y(f), a)
}