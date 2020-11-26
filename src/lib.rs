#![no_std]
#![warn(missing_docs)]

//! Allocation-free data structures with constant capacity.

pub mod arena;

pub use crate::arena::{Arena, Box};

#[cfg(feature = "tinyvec")]
pub use tinyvec::{ArrayVec, SliceVec};
