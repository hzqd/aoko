use core::marker::PhantomData;
use alloc::{string::String, format};

pub trait Monoid {
    type Unit;
    type Ret;

    fn unit() -> Self::Unit;

    fn merge(some: Self::Unit, other: Self::Unit) -> Self::Ret;
}

macro_rules! impl_str_monoid {
    ($($id:ident, $ex:expr);* $(;)?) => {$(
        pub struct $id<'a>(PhantomData<&'a ()>);

        impl<'a> Monoid for $id<'a> {
            type Unit = &'a str;
            type Ret = String;

            fn unit() -> Self::Unit { $ex }

            fn merge(some: Self::Unit, other: Self::Unit) -> Self::Ret {
                format!("{}{}{}", some, Self::unit(), other)
            }
        }
    )*};
}

impl_str_monoid! {      StrEmpty, "";
    StrDot, ".";        StrSlash, "/";
    StrAdd, "+";        StrPercent, "%";
    StrSub, "-";        StrBackslash, "\\";
    StrMul, "*";        StrUnderscore, "_";
}

macro_rules! impl_integer_monoid {
    ($($ty:ty, $id:ident, $ex:expr);* $(;)?) => {$(
        pub struct $id;

        impl Monoid for $id {
            type Unit = $ty;
            type Ret = Self::Unit;

            fn unit() -> Self::Unit { $ex }

            fn merge(some: Self::Unit, other: Self::Unit) -> Self::Ret {
                match Self::unit() {
                    0 => some + other,
                    1 => some * other,
                    _ => panic!("Unsupport Unit")
                }
            }
        }
    )*};
}

impl_integer_monoid! {
    u8, U8Add, 0;       i8, I8Add, 0;           u8, U8Mul, 1;       i8, I8Mul, 1;
    u16, U16Add, 0;     i16, I16Add, 0;         u16, U16Mul, 1;     i16, I16Mul, 1;
    u32, U32Add, 0;     i32, I32Add, 0;         u32, U32Mul, 1;     i32, I32Mul, 1;
    u64, U64Add, 0;     i64, I64Add, 0;         u64, U64Mul, 1;     i64, I64Mul, 1;
    usize, UsizeAdd, 0; isize, IsizeAdd, 0;     usize, UsizeMul, 1; isize, IsizeMul, 1;
    u128, U128Add, 0;   i128, I128Add, 0;       u128, U128Mul, 1;   i128, I128Mul, 1;
}

#[cfg(test)]
mod test {
    use crate::assert_eqs;
    use super::{Monoid, StrDot, U8Add, U8Mul};

    #[test]
    fn test_all() {
        assert_eqs! {
            "a.b", StrDot::merge("a", "b");
            5, U8Add::merge(2, 3);
            6, U8Mul::merge(2, 3);
        }
    }
}