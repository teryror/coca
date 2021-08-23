#![no_std]
#![doc(html_root_url = "https://docs.rs/coca/0.2.0")]
#![cfg_attr(docs_rs, feature(doc_cfg))]
#![cfg_attr(feature = "unstable", feature(unsize))]
#![cfg_attr(feature = "unstable", feature(set_ptr_value))]
#![warn(missing_docs)]
#![warn(clippy::pedantic)]
#![allow(
    clippy::inline_always,
    clippy::missing_errors_doc,
    clippy::module_name_repetitions,
    clippy::must_use_candidate,
    clippy::shadow_unrelated
)]

//! Allocation-free data structures with constant capacity.
//!
//! Designed for use in memory-constrained embedded systems that cannot use
//! growable structures, and in soft real-time applications that cannot tolerate
//! latency spikes caused by reallocations.
//!
//! These generally require the user to supply memory to work with.
//!
//! # Features
//! - `profile`: Enables memory profiling in arenas; see the
//!   [module-level documentation](arena#memory-profiling) for details.
//! - `alloc`: Adds trait implementations and convenience functions for working
//!   with heap allocated memory.
//! - `unstable`: Enables the [`object`] module, which relies on unstable features,
//!   namely `feature(unsize)` and `feature(set_ptr_value)`.

#[cfg(feature = "alloc")]
#[doc(hidden)]
pub extern crate alloc;

pub mod arena;
pub mod binary_heap;
pub mod deque;
pub mod option_group;
pub mod pool;
pub mod storage;
pub mod vec;

#[cfg(feature = "unstable")]
#[cfg_attr(docs_rs, doc(cfg(feature = "unstable")))]
pub mod object;

pub use crate::{
    arena::{Arena, Box},
    binary_heap::{ArenaHeap, SliceHeap},
    deque::{ArenaDeque, SliceDeque},
    option_group::{OptionGroup8, OptionGroup16},
    vec::{ArenaVec, SliceVec},
};

pub use crate::{
    binary_heap::{InlineHeap, TiInlineHeap},
    deque::{InlineDeque, TiInlineDeque},
    vec::{InlineVec, TiInlineVec},
};

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub use crate::{binary_heap::AllocHeap, deque::AllocDeque, vec::AllocVec};

#[cfg(feature = "unstable")]
#[cfg_attr(docs_rs, doc(cfg(feature = "unstable")))]
pub use crate::object::InlineObject;
