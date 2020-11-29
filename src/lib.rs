#![no_std]
#![cfg_attr(feature = "nightly", feature(min_const_generics))]
#![cfg_attr(docs_rs, feature(doc_cfg))]
#![warn(missing_docs)]

//! Allocation-free data structures with constant capacity.
//!
//! Designed for use in memory-constrained embedded systems that cannot use
//! growable structures, and in soft-realtime applications that cannot tolerate
//! latency spikes caused by reallocations.
//!
//! These generally require the user to supply memory to work with.
//!
//! # Features
//! - `nightly`: Adds trait implementations and convenience functions that require
//!   the nightly-only `feature(min_const_generics)`, allowing inlining of
//!   [`ContiguousStorage`](storage::ContiguousStorage).
//! - `alloc`: Adds trait implementations and convenience functions for working
//!   with heap allocated memory.

#[cfg(feature = "alloc")]
#[doc(hidden)]
pub extern crate alloc;

pub mod arena;
pub mod storage;
pub mod vec;

pub use crate::arena::{Arena, Box};

#[cfg(feature = "alloc")]
pub use crate::storage::HeapStorage;
#[cfg(feature = "nightly")]
pub use crate::storage::InlineStorage;
pub use crate::storage::{ArenaStorage, SliceStorage};

pub use crate::vec::SliceVec;
#[cfg(feature = "nightly")]
pub use crate::vec::{ArrayVec, TiArrayVec};
