#![no_std]
#![feature(impl_trait_in_fn_trait_return)]
#![feature(return_position_impl_trait_in_trait)]
extern crate alloc;
pub mod no_std;

#[cfg(feature = "std")]
extern crate no_std_compat as std;

#[cfg(feature = "std")]
pub mod standard;