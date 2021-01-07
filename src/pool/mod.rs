//! Pool-based memory management.

pub mod direct;

use core::hash::Hash;

use crate::storage::Capacity;

/// Stable references to values stored in a pool.
pub unsafe trait Handle: Copy + Eq + Hash + Ord {
    type Index: Capacity;

    unsafe fn new(index: usize, generation: u32) -> Self;
    fn into_raw_parts(self) -> (usize, u32);
}
