#![no_std]
#![doc(html_root_url = "https://docs.rs/coca/0.1.0")]
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
//! - `profile`: Enables memory profiling in arenas; see the
//!   [module-level documentation](arena#memory-profiling) for details.
//! - `nightly`: Adds trait implementations and convenience functions that require
//!   the nightly-only `feature(min_const_generics)`, allowing inlining of
//!   [`ContiguousStorage`](storage::ContiguousStorage).
//! - `alloc`: Adds trait implementations and convenience functions for working
//!   with heap allocated memory.

#[cfg(feature = "alloc")]
#[doc(hidden)]
pub extern crate alloc;

pub mod arena;
pub mod binary_heap;
pub mod storage;
pub mod vec;

pub use crate::arena::{Arena, Box};

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub use crate::binary_heap::AllocHeap;
pub use crate::binary_heap::{ArenaHeap, SliceHeap};
#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
pub use crate::binary_heap::{ArrayHeap, TiArrayHeap};

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub use crate::vec::AllocVec;
pub use crate::vec::{ArenaVec, SliceVec};
#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
pub use crate::vec::{ArrayVec, TiArrayVec};
