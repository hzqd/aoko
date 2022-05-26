use core::{ops::{Add, Sub, Mul, Div, Rem, Neg, Not, Shl, Shr, BitAnd, BitOr, BitXor}, cmp::Ordering};

/// The continuation supporting for operators
pub trait Op<R>: Sized {
    /// The continuation supporting for Add operator
    /// 
    /// # Examples
    /// 
    /// ```
    /// use aoko::no_std::cps::operators::Op;
    /// 
    /// assert_eq!(3, 1.add_c(1, |n| n + 1));
    /// ```
    #[inline(always)]
    fn add_c(self, other: Self, k: impl FnOnce(Self::Output) -> R) -> R where Self: Add {
        k(self + other)
    }

    /// The continuation supporting for Sub operator
    /// 
    /// # Examples
    /// 
    /// ```
    /// use aoko::no_std::cps::operators::Op;
    /// 
    /// fn fibonacci(n: u8, k: &dyn Fn(u8) -> u8) -> u8 {
    ///     match n {
    ///         0 => k(0),
    ///         1 => k(1),
    ///         _ => n.sub_c(1, |x| fibonacci(x, &|r1| n.sub_c(2, |y| fibonacci(y, &|r2| r1.add_c(r2, k)))))
    ///     }
    /// }
    /// 
    /// assert_eq!(5, fibonacci(10, &|result| result - 50));
    /// ```
    #[inline(always)]
    fn sub_c(self, other: Self, k: impl FnOnce(Self::Output) -> R) -> R where Self: Sub {
        k(self - other)
    }

    /// The continuation supporting for Mul operator
    /// 
    /// # Examples
    /// 
    /// ```
    /// use aoko::no_std::cps::operators::Op;
    /// 
    /// fn factorial(n: u8, k: &dyn Fn(u8) -> u8) -> u8 {
    ///     match n {
    ///         0 => k(1),
    ///         _ => n.sub_c(1, |x| factorial(x, &|y| y.mul_c(n, k)))
    ///     }
    /// }
    /// 
    /// assert_eq!(20, factorial(5, &|result| result - 100));
    /// ```
    #[inline(always)]
    fn mul_c(self, other: Self, k: impl FnOnce(Self::Output) -> R) -> R where Self: Mul {
        k(self * other)
    }

    /// The continuation supporting for Div operator
    /// 
    /// # Examples
    /// 
    /// ```
    /// use aoko::no_std::cps::operators::Op;
    /// 
    /// assert_eq!(10, 15.div_c(3, |n| n * 2));
    /// ```
    #[inline(always)]
    fn div_c(self, other: Self, k: impl FnOnce(Self::Output) -> R) -> R where Self: Div {
        k(self / other)
    }

    /// The continuation supporting for Rem operator
    /// 
    /// # Examples
    /// 
    /// ```
    /// use aoko::no_std::cps::operators::Op;
    /// 
    /// assert_eq!(9, 3.rem_c(2, |n| n + 8));
    /// ```
    #[inline(always)]
    fn rem_c(self, other: Self, k: impl FnOnce(Self::Output) -> R) -> R where Self: Rem {
        k(self % other)
    }

    /// The continuation supporting for Neg operator
    #[inline(always)]
    fn neg_c(self, k: impl FnOnce(Self::Output) -> R) -> R where Self: Neg {
        k(self.neg())
    }

    /// The continuation supporting for Not operator
    #[inline(always)]
    fn not_c(self, k: impl FnOnce(Self::Output) -> R) -> R where Self: Not {
        k(self.not())
    }

    /// The continuation supporting for Shl operator
    #[inline(always)]
    fn shl_c(self, other: Self, k: impl FnOnce(Self::Output) -> R) -> R where Self: Shl {
        k(self << other)
    }

    /// The continuation supporting for Shr operator
    #[inline(always)]
    fn shr_c(self, other: Self, k: impl FnOnce(Self::Output) -> R) -> R where Self: Shr {
        k(self >> other)
    }

    /// The continuation supporting for BitAnd operator
    #[inline(always)]
    fn bit_and_c(self, other: Self, k: impl FnOnce(Self::Output) -> R) -> R where Self: BitAnd {
        k(self & other)
    }

    /// The continuation supporting for BitOr operator
    #[inline(always)]
    fn bit_or_c(self, other: Self, k: impl FnOnce(Self::Output) -> R) -> R where Self: BitOr {
        k(self | other)
    }

    /// The continuation supporting for BitXor operator
    #[inline(always)]
    fn bit_xor_c(self, other: Self, k: impl FnOnce(Self::Output) -> R) -> R where Self: BitXor {
        k(self ^ other)
    }

    /// The continuation supporting for the cmp function of Ord operator
    #[inline(always)]
    fn cmp_c(&self, other: &Self, k: impl FnOnce(Ordering) -> R) -> R where Self: Ord {
        k(self.cmp(other))
    }
}

impl<T, R> Op<R> for T {}