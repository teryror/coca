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
    clippy::wildcard_imports,
)]

//! The `coca` crate provides collection types and other facilities for managing
//! memory without using the [`alloc` crate](https://doc.rust-lang.org/alloc/index.html).
//! 
//! ## Data Structures with Constant Capacity
//! 
//! Typical container implementations manage their own memory behind the scenes,
//! calling the global allocator (or a user-provided one, using the as yet
//! unstable [`Allocator` API](alloc::alloc::Allocator)) as needed when they
//! are modified.
//! 
//! This is convenient, but it does have some drawbacks to be aware of:
//! 
//! * reallocation may be slow, especially if the data structure is large and
//!   a lot of data has to be moved around,
//! * memory usage is essentially unbounded and must be carefully managed, should
//!   this pose a problem,
//! * such implementations simply cannot be used when no allocator is available,
//!   as may be the case in embedded systems.
//! 
//! In contrast, the data structures provided by `coca` do **not** work this way.
//! They operate on a given block of memory, and never reallocate. This means
//! that operations that grow a data structure may fail if the available space
//! is insufficient. For all such operations, two methods are provided: one,
//! returning a [`Result`](core::result::Result), has its name prefixed with
//! `try_`, the other, without the name prefix, being a wrapper that panics in
//! the error case.
//! 
//! Client code, then, has to either guarantee that the given memory block's
//! capacity will never be exceeded, or handle the failure case gracefully.
//! 
//! ## The `Storage` Abstraction
//! 
//! In `coca`, there is no single way of supplying a data structure with working
//! memory. Instead, most containers have a generic type parameter `S` bound by
//! the [`Storage` trait](storage::Storage), which is the type of the memory
//! block to be used. `Storage`, in turn, has a type parameter `R`, bound by
//! the [`LayoutSpec` trait](storage::LayoutSpec), which is used to describe
//! the memory [`Layout`](core::alloc::Layout) required by that container.
//! 
//! For instance, data structures built on an array (such as [`Vec`](collections::vec::Vec)
//! or [`String`](string::String)) require `S: Storage<ArrayLayout<T>>`, which is
//! implemented for standard arrays and slices, among others, while more complex
//! data structures (such as [`DirectPool`](collections::pool::direct::DirectPool))
//! have unique layout requirements (in this case `S: Storage<DirectPoolLayout<T, H>>`)
//! which are only fulfilled by purpose-built types.
//! 
//! No matter the layout requirements, for each data structure, the following
//! storage strategies are available:
//! 
//! * `InlineStorage`, defined as a [partially initialized array](storage::InlineStorage)
//!   or as purpose-built `struct`s for non-array-like data structures (e.g.
//!   [`collections::pool::direct::InlineStorage`]), requires the capacity to
//!   be truly `const`, i.e. statically known at compile time; this allows
//!   storing the contents inline with the top-level `struct` type, with no
//!   indirection, and thus entirely on the stack, for example.
//! * [`ArenaStorage`] is a (pointer, capacity) pair referencing an
//!   [arena-allocated](arena) block of memory, bounding the lifetime of the
//!   data structure to the lifetime of the `Arena`, but supports dynamically
//!   chosen capacities.
//! * Likewise, [`AllocStorage`](storage::AllocStorage) references a block of
//!   memory from the global allocator, requiring the `alloc` crate.
//! 
//! Note that, depending on the choice of storage type, available functionality
//! may differ slightly. For example, the [`Clone`] trait is only implemented
//! on data structures using `InlineStorage` or `AllocStorage`, but not
//! `ArenaStorage`.
//! 
//! Since concrete type names quickly become unwieldy in this scheme, `coca`
//! provides type aliases such as [`InlineVec`](collections::InlineVec),
//! [`ArenaVec`](collections::ArenaVec), and [`AllocVec`](collections::AllocVec)
//! for all of its data structures.
//! 
//! ## The `Capacity` Trait
//! 
//! Compared to the standard implementations, most of `coca`'s data structures
//! have one more additional type parameter, which is bound by the
//! [`Capacity` trait](storage::Capacity). This type used to index into the
//! data structure and to represent its size at runtime. It generally defaults
//! to `usize`, but `Capacity` is also implemented for `u8`, `u16`, `u32` and
//! `u64`.
//! 
//! This gives client code even more control over the exact size of the data
//! structure, but it has one additional advantage: using the [`index_type`]
//! macro, new types implementing the `Capacity` trait can be generated, which
//! then allows using different index types with different collections,
//! potentially preventing accidental use of the wrong index.
//! 
//! ## Cargo Features
//! 
//! - `alloc`: Enables an optional dependency on the `alloc` crate and adds
//!   the [`AllocStorage`](storage::AllocStorage) type, as well as other trait
//!   implementations and convenience functions for using the global allocator.
//! - `unstable`: Adds the [`object`] module providing a statically-sized
//!   container for dynamically-sized types. This relies on the unstable
//!   `feature(unsize)` and `feature(set_ptr_value)` and thus requires a nightly
//!   compiler.
//! - `profile`: Adds memory profiling in arena allocators. See the
//!   [module-level documentation](arena#memory-profiling) for details.
//! 
//! None of these features are enabled by default.

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
use crate::storage::{ArenaStorage, ArrayLayout, InlineStorage, SliceStorage};

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
pub type ArenaString<'a, I = usize> = String<ArenaStorage<'a, ArrayLayout<u8>>, I>;

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
pub type AllocString<I = usize> = String<crate::storage::AllocStorage<ArrayLayout<u8>>, I>;

/// A string using an inline array for storage.
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