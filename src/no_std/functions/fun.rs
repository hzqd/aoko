use alloc::string::String;
use core::ops::BitXorAssign;

/// Conveniently create String variable.
/// 
/// # Examples
/// 
/// ```
/// use aoko::no_std::functions::fun::s;
/// 
/// let s: String = s("Rust");
/// ```
pub fn s(x: impl Into<String>) -> String {
    x.into()
}

/// Swaps two variables' value.
/// 
/// # Warnings
/// 
/// * Do not swap variables with a same memory address, otherwise you will get `0`.
/// 
/// # Examples
/// ```
/// use aoko::no_std::functions::fun::*;
/// 
/// // Normal:
/// let a = &mut 1024; let b = &mut 2048;
/// swap_xor(a, b);
/// assert_eq!((2048, 1024), (*a, *b));
/// 
/// // Warning:
/// let c = &mut 3072 as *mut i32;
/// let x = unsafe { &mut *c };
/// let y = unsafe { &mut *c };
/// swap_xor(x, y);
/// assert_eq!((0, 0), (*x, *y))
/// ```
pub fn swap_xor<T>(a: &mut T, b: &mut T) where T: BitXorAssign<T> + Copy {
    *a ^= *b;
    *b ^= *a;
    *a ^= *b;
}