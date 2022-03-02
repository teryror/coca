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
pub mod collections;
pub mod storage;
pub mod string;

#[cfg(feature = "unstable")]
#[cfg_attr(docs_rs, doc(cfg(feature = "unstable")))]
pub mod object;

#[cfg(feature = "unstable")]
#[cfg_attr(docs_rs, doc(cfg(feature = "unstable")))]
pub use crate::object::InlineObject;

use crate::string::String;
use crate::storage::{ArenaStorage, ArrayLike, InlineStorage, SliceStorage};

/// A string using any mutable byte slice for storage.
/// 
/// # Examples
/// ```
/// let mut buf = [core::mem::MaybeUninit::<u8>::uninit(); 8];
/// let str = coca::SliceString::<'_, usize>::from(&mut buf[..6]);
/// 
/// assert_eq!(str.capacity(), 6);
/// ```
pub type SliceString<'a, I = usize> = String<SliceStorage<'a, u8>, I>;
/// A string using an arena-allocated byte slice for storage.
/// 
/// # Examples
/// ```
/// use coca::arena::Arena;
/// use coca::ArenaString;
/// use core::mem::MaybeUninit;
///
/// let mut backing_region = [MaybeUninit::uninit(); 160];
/// let mut arena = Arena::from(&mut backing_region[..]);
///
/// let s: ArenaString<'_, usize> = arena.try_with_capacity(100).unwrap();
/// assert!(arena.try_with_capacity::<_, ArenaString<'_, usize>>(100).is_none());
/// ```
pub type ArenaString<'a, I = usize> = String<ArenaStorage<'a, ArrayLike<u8>>, I>;

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
/// A string using a heap-allocated slice for storage.
/// 
/// # Examples
/// ```
/// let mut s = coca::AllocString::with_capacity(16usize);
/// s.push_str("Hello, ");
/// s.push_str("World!");
/// 
/// assert_eq!(s, "Hello, World!");
/// ```
pub type AllocString<I = usize> = String<crate::storage::AllocStorage<ArrayLike<u8>>, I>;

/// A string using an inline array for storage, generic over the index type.
/// 
/// # Examples
/// ```
/// let mut s = coca::InlineString::<255, u8>::new();
/// assert_eq!(s.capacity(), 255);
/// assert!(s.is_empty());
/// ```
pub type InlineString<const C: usize, I = usize> = String<InlineStorage<u8, C>, I>;

/// The error type for many operations on data structures with constant capacity.
/// 
/// When working with data structures of limited capacity, insertions may fail
/// due to insufficient remaining space. In `coca`, insertion methods generally
/// have a name starting with `try`, and return a [`Result`](core::result::Result).
/// For convenience, panicking wrappers without the `try` prefix are also provided.
/// 
/// In many cases, such as e.g. [`Vec::try_push`](crate::collections::vec::Vec::try_push),
/// the value to be inserted is returned back to the caller when the operation fails;
/// in some cases, this is unnecessary (e.g. when ownership is not transferred, as with
/// [`Vec::try_extend_from_slice`](crate::collections::vec::Vec::try_extend_from_slice))
/// or would result in unwieldy type signatures. Such methods use this unit error type
/// instead.
#[derive(Copy, Clone, Debug, Default)]
pub struct CapacityError;

impl CapacityError {
    #[inline(always)]
    pub(crate) fn new<T>() -> core::result::Result<T, CapacityError> {
        Err(Self)
    }
}

/// A specialized [`Result`](core::result::Result) type for operations on data structures with constant capacity.
/// 
/// This type is broadly used across `coca` for most operations which grow a data structure.
/// 
/// This type definition is generally used to avoid writing out [`CapacityError`] directly and is otherwise a direct mapping to [`core::result::Result`].
pub type Result<T> = core::result::Result<T, CapacityError>;

#[cfg(test)]
mod test_utils {
    use core::cell::Cell;

    #[cfg(target_pointer_width = "64")]
    pub(crate) const RNG_SEED: [u8; 32] = [
        0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0,
        0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0,
    ];
    #[cfg(not(target_pointer_width = "64"))]
    pub(crate) const RNG_SEED: [u8; 16] = [
        0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0,
    ];

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