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
    binary_heap::{ArenaHeap, InlineHeap, SliceHeap, TiInlineHeap},
    deque::{ArenaDeque, InlineDeque, SliceDeque, TiInlineDeque},
    option_group::{OptionGroup8, OptionGroup16, OptionGroup32, OptionGroup64},
    pool::direct::{DirectArenaPool, DirectInlinePool, TiDirectInlinePool},
    pool::packed::{PackedArenaPool, PackedInlinePool, TiPackedInlinePool},
    vec::{ArenaVec, InlineVec, SliceVec, TiInlineVec},
};

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub use crate::{binary_heap::AllocHeap, deque::AllocDeque, pool::direct::DirectAllocPool, pool::packed::PackedAllocPool, vec::AllocVec};

#[cfg(feature = "unstable")]
#[cfg_attr(docs_rs, doc(cfg(feature = "unstable")))]
pub use crate::object::InlineObject;

#[cfg(test)]
mod test_utils {
    use core::cell::Cell;

    #[derive(Debug)]
    pub(crate) struct DropCounter {
        drop_count: Cell<usize>,
    }

    impl DropCounter {
        pub(crate) fn new() -> Self {
            DropCounter { drop_count: Cell::new(0), }
        }

        pub(crate) fn new_droppable<T>(&self, value: T) -> Droppable<'_, T> {
            Droppable { counter: self, value }
        }

        pub(crate) fn dropped(&self) -> usize {
            self.drop_count.get()
        }
    }

    #[derive(Debug)]
    pub(crate) struct Droppable<'a, T = ()>{
        counter: &'a DropCounter,
        pub value: T,
    }

    impl<'a, T> Drop for Droppable<'a, T> {
        fn drop(&mut self) {
            let new_drop_count = self.counter.drop_count.get() + 1;
            self.counter.drop_count.set(new_drop_count);
        }
    }
}