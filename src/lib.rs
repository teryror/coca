#![no_std]
#![cfg_attr(feature = "nightly", feature(min_const_generics))]
#![warn(missing_docs)]

//! Allocation-free data structures with constant capacity.

pub mod arena;
pub mod list;

pub use crate::arena::{Arena, Box};
pub use crate::list::{ArrayList, List, TiArrayList};
