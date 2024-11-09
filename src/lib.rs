//! Small, barebones JSON parser that works well with `no_std` and `const`.
//!
//! Currently requires Rust 1.83.

#![cfg_attr(not(test), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

pub mod source;
pub(crate) mod util;
