#![no_std]
#![allow(incomplete_features)]
extern crate alloc;
pub mod no_std;

#[cfg(feature = "std")]
extern crate no_std_compat as std;

#[cfg(feature = "std")]
pub mod standard;