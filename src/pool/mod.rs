//! Pool-based memory management.

pub mod direct;

use core::fmt::Debug;
use core::hash::Hash;
use core::num::NonZeroU64;

use crate::storage::Capacity;

/// Stable references to values stored in a pool.
pub unsafe trait Handle: Copy + Debug + Eq + Hash + Ord {
    type Index: Capacity;

    unsafe fn new(index: usize, generation: u32) -> Self;
    fn into_raw_parts(self) -> (usize, u32);
}

/// The default handle type, with 32 bits each for the index and generation count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefaultHandle(NonZeroU64);
unsafe impl Handle for DefaultHandle {
    type Index = u32;

    unsafe fn new(index: usize, generation: u32) -> Self {
        debug_assert!(index <= Self::Index::MAX_REPRESENTABLE);
        debug_assert_eq!(generation % 2, 1);
        let assembled = index as u64 & 0xFFFF_FFFF | ((generation as u64) << 32);
        DefaultHandle(NonZeroU64::new_unchecked(assembled))
    }

    fn into_raw_parts(self) -> (usize, u32) {
        let raw: u64 = self.0.into();
        let index = (raw & 0xFFFF_FFFF) as usize;
        let generation = (raw >> 32) as u32;
        (index, generation)
    }
}
