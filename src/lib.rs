#![no_std]
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
//! - [`tinyvec`] (optional dependency): Implements convenience methods on
//!   `Arena` for allocating `SliceVec`.
//! - [`alloc`]: Implements [`HeapRegion`] for more convenient initialization.
//!   Also enables `tinyvec/alloc`.

#[cfg(feature = "alloc")]
#[doc(hidden)]
pub extern crate alloc;

pub mod arena;
pub use crate::arena::{Arena, Box};

/// Re-export of [`tinyvec`].
#[cfg(feature = "tinyvec")]
pub mod vec {
    #[cfg(feature = "alloc")]
    pub use tinyvec::TinyVec;
    pub use tinyvec::{ArrayVec, SliceVec};
}

#[cfg(feature = "alloc")]
mod heapregion {
    use core::mem::MaybeUninit;

    use alloc::{boxed::Box, vec};
    /// A heap allocated buffer for convenient initialization of coca structures.
    ///
    /// Requires the `alloc` feature.
    ///
    /// # Examples
    /// ```
    /// use coca::{Arena, HeapRegion};
    /// let mut backing_region = HeapRegion::with_capacity(1024 * 1024);
    /// let arena = Arena::from_buffer(backing_region.as_mut());
    /// ```
    pub struct HeapRegion<T = u8> {
        buf: Box<[MaybeUninit<T>]>,
    }
    impl<T: Copy> HeapRegion<T> {
        /// Allocates memory on the heap and leaves it uninitialized.
        pub fn with_capacity(cap: usize) -> Self {
            // TODO: remove Copy bound by using `new_uninit_slice` once that is stable
            // see https://github.com/rust-lang/rust/issues/63291
            HeapRegion {
                buf: vec![MaybeUninit::uninit(); cap].into_boxed_slice(),
            }
        }
    }
    impl<T> core::convert::AsMut<[MaybeUninit<T>]> for HeapRegion<T> {
        fn as_mut(&mut self) -> &mut [MaybeUninit<T>] {
            &mut self.buf[..]
        }
    }
}

#[cfg(feature = "alloc")]
pub use crate::heapregion::*;
