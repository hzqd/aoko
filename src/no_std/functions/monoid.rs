use core::marker::PhantomData;
use alloc::{string::String, format};

pub trait NotMonoid {
    type Unit;
    type P1;
    type P2;
    type Ret;

    fn unit() -> Self::Unit;
    fn merge(some: Self::P1, other: Self::P2) -> Self::Ret;
}

macro_rules! impl_str_not_monoid {
    ($($id:ident, $ex:expr);* $(;)?) => {$(
        pub struct $id<'a>(PhantomData<&'a ()>);

        impl<'a> NotMonoid for $id<'a> {
            // Unit = P1 = P2 = &'a str
            // Ret = String
            type Unit = &'a str;
            type P1 = Self::Unit;
            type P2 = Self::P1;
            type Ret = String;

            fn unit() -> Self::Unit { $ex }

            fn merge(some: Self::P1, other: Self::P2) -> Self::Ret {
                format!("{}{}{}", some, Self::unit(), other)
            }
        }
    )*};
}

impl_str_not_monoid! {  StrEmpty, "";
    StrDot, ".";        StrSlash, "/";
    StrAdd, "+";        StrPercent, "%";
    StrSub, "-";        StrBackslash, "\\";
    StrMul, "*";        StrUnderscore, "_";
}

macro_rules! impl_num_not_monoid {
    ($($ty:ty, $id:ident, $ex:expr);* $(;)?) => {$(
        pub struct $id;

        impl NotMonoid for $id {
            type Unit = u8;
            // P1 = P2 = Ret
            type P1 = $ty;
            type P2 = Self::P1;
            type Ret = Self::P2;

            fn unit() -> Self::Unit { $ex }

            fn merge(some: Self::P1, other: Self::P2) -> Self::Ret {
                match Self::unit() {
                    0 => some + other,
                    1 => some * other,
                    _ => panic!("Unsupport Unit")
                }
            }
        }
    )*};
}

impl_num_not_monoid! {
    u8, U8Add, 0;       i8, I8Add, 0;                               u8, U8Mul, 1;       i8, I8Mul, 1;
    u16, U16Add, 0;     i16, I16Add, 0;                             u16, U16Mul, 1;     i16, I16Mul, 1;
    u32, U32Add, 0;     i32, I32Add, 0;     f32, F32Add, 0;         u32, U32Mul, 1;     i32, I32Mul, 1;     f32, F32Mul, 1;
    u64, U64Add, 0;     i64, I64Add, 0;     f64, F64Add, 0;         u64, U64Mul, 1;     i64, I64Mul, 1;     f64, F64Mul, 1;
    usize, UsizeAdd, 0; isize, IsizeAdd, 0;                         usize, UsizeMul, 1; isize, IsizeMul, 1;
    u128, U128Add, 0;   i128, I128Add, 0;                           u128, U128Mul, 1;   i128, I128Mul, 1;
}

#[cfg(test)]
mod test {
    use crate::assert_eqs;
    use super::*;

    #[test]
    fn test_all() {
        assert_eqs! {
            "a.b", StrDot::merge("a", "b");
            5, U8Add::merge(2, 3);
            6, U8Mul::merge(2, 3);
            4.6,  F64Add::merge(1.2, 3.4);
            4.08, F64Mul::merge(1.2, 3.4);
        }
    }
}