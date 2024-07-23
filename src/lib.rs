#![no_std]
#![allow(incomplete_features)]
extern crate alloc;
pub mod no_std;

extern crate no_std_compat2 as std;

#[cfg(feature = "std")]
pub mod standard;