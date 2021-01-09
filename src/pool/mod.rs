//! Pool-based memory management.
//!
//! A pool takes ownership of inserted values and returns unique, stable handles
//! that can be used to refer back to those same values later on. While it is
//! safe to index into a pool with a handle obtained from a different one, this
//! is nonsensical; to avoid this mistake, users may define custom handle types
//! using the [`handle_type!`] macro.
//!
//! Each handle contains a generation identifier, so that, should a value be
//! removed and a new one be inserted at the same location, the old handle
//! remains invalid.
//!
//! Note that the generation count may overflow, so this cannot be strictly
//! guaranteed for arbitrarily long sequences of insertions and deletions.
//! 64-bit handles use 32-bit generation identifiers, making such errors highly
//! unlikely. Care must be taken with 32-bit handles, however, which may use as
//! few as 16 bits:
//!
//! ```
//! # use coca::handle_type;
//! handle_type! { TinyHandle: 16 / 32; }
//!
//! # let mut storage = [core::mem::MaybeUninit::uninit(); 128];
//! # let mut arena = coca::Arena::from(&mut storage[..]);
//! let mut pool = arena.direct_pool::<&'static str, TinyHandle>(4);
//! let first = pool.insert("this was first");
//!
//! let mut last_handle = first;
//! for _ in 0..0x8000 {
//!     pool.remove(last_handle);
//!     last_handle = pool.insert("this is not first");
//! }
//!
//! assert_eq!(pool[first], "this is not first");
//! ```

pub mod direct;

use core::fmt::Debug;
use core::hash::Hash;

use crate::storage::Capacity;

/// Stable references to values stored in a pool.
///
/// # Safety
/// Implementors must ensure that the following restrictions are met:
///
/// * `Handle::new(i, g).into_raw_parts() == (i, g)` for all `i <= MAX_INDEX, g <= MAX_GENERATION`,
/// * `MAX_INDEX` must be less than or equal to `Index::MAX_REPRESENTABLE`,
/// * `MAX_GENERATION` must be one less than a power of two.
///
/// Using [`handle_type!`] should be preferred over implementing this manually.
pub unsafe trait Handle: Copy + Debug + Eq + Hash + Ord {
    /// The type pools should use for indices into their storage space.
    type Index: Capacity;
    /// The maximum representable index; the maximum capacity of a pool using
    /// this handle type is equal to `MAX_INDEX - 1` because the maximum index
    /// is reserved as a sentinel value.
    const MAX_INDEX: usize;
    /// The maximum representable generation count.
    const MAX_GENERATION: u32;

    /// Constructs a new handle from the storage location and generation count.
    unsafe fn new(index: usize, generation: u32) -> Self;
    /// Returns the storage location and generation count packed into the handle.
    fn into_raw_parts(self) -> (usize, u32);
}

#[cold]
#[inline(never)]
#[track_caller]
pub(crate) fn buffer_too_large_for_handle_type<H: Handle>() {
    panic!(
        "provided storage block cannot be fully indexed by type {} (max capacity is {})",
        core::any::type_name::<H>(),
        H::MAX_INDEX - 1,
    );
}

/// Generates one or more new types implementing [`Handle`].
///
/// This can help in avoiding use of the wrong handle with an object pool.
///
/// This macro takes a semicolon-separated list, where each entry must match
/// one of two formats:
///
/// * `($meta)* ($vis)? $name: 64` generates a handle type that is identical to
///   [`DefaultHandle`], with 32 bits each for the index and generation.
/// * `($meta)* ($vis)? $name: $i / 32` generates a 32-bit handle with `$i`
///   bits used for the index, and the remainder used for the generation count.
///
/// `($meta)*` stands for any number of attributes, including doc comments, and
/// `($vis)?` is an optional visibility specifier (i.e. `pub` or `pub(crate)`).
///
/// # Examples
/// ```
/// use coca::{handle_type, pool::Handle};
/// handle_type! {
///     A: 12 / 32;
///     /// Documentation for `B` goes here.
///     pub B: 16 / 32;
///     D: 64;
/// }
///
/// assert_eq!(A::MAX_INDEX, 4095);
/// assert_eq!(A::MAX_GENERATION, 1_048_575);
///
/// assert_eq!(B::MAX_INDEX, 65535);
/// assert_eq!(B::MAX_GENERATION, 65535);
///
/// assert_eq!(D::MAX_INDEX, 4_294_967_295);
/// assert_eq!(D::MAX_GENERATION, 4_294_967_295);
/// ```
/// Note that the maximum number of bits you can reserve for the index is 16.
/// This is enforced with a static assertion:
/// ```compile_fail
/// # use coca::handle_type;
/// handle_type!{ C: 20 / 32; } // attempt to compute `0_usize - 1_usize`, which would overflow
/// ```
#[macro_export]
macro_rules! handle_type {
    ( $(#[$attrs:meta])* $v:vis $name:ident: 64 ; $($rest:tt)* ) => {
        $(#[$attrs])*
        #[derive(
            core::marker::Copy,
            core::clone::Clone,
            core::fmt::Debug,
            core::hash::Hash,
            core::cmp::PartialEq,
            core::cmp::Eq,
            core::cmp::PartialOrd,
            core::cmp::Ord)]
        #[repr(transparent)]
        $v struct $name(core::num::NonZeroU64);

        impl $name {
            /// Returns a handle that is guaranteed to always be invalid.
            #[allow(dead_code)]
            $v const fn null() -> Self {
                unsafe { $name(core::num::NonZeroU64::new_unchecked(0xFFFF_FFFF)) }
            }
        }

        unsafe impl $crate::pool::Handle for $name {
            type Index = u32;
            const MAX_INDEX: usize = 0xFFFF_FFFF;
            const MAX_GENERATION: u32 = 0xFFFF_FFFF;
            unsafe fn new(index: usize, generation: u32) -> Self {
                debug_assert!(index <= Self::MAX_INDEX);
                debug_assert_eq!(generation % 2, 1);
                let assembled = index as u64 & 0xFFFF_FFFF | ((generation as u64) << 32);
                $name(core::num::NonZeroU64::new_unchecked(assembled))
            }
            fn into_raw_parts(self) -> (usize, u32) {
                let raw: u64 = self.0.into();
                let index = (raw & 0xFFFF_FFFF) as usize;
                let generation = (raw >> 32) as u32;
                (index, generation)
            }
        }

        handle_type!($($rest)*);
    };
    ( $(#[$attrs:meta])* $v:vis $name:ident: $n:literal / 32 ; $($rest:tt)* ) => {
        #[allow(unknown_lints, eq_op)]
        const _: [(); 0 - !{ const ASSERT: bool = $n <= 16; ASSERT } as usize] = []; // static assertion

        $(#[$attrs])*
        #[derive(
            core::marker::Copy,
            core::clone::Clone,
            core::fmt::Debug,
            core::hash::Hash,
            core::cmp::PartialEq,
            core::cmp::Eq,
            core::cmp::PartialOrd,
            core::cmp::Ord)]
        #[repr(transparent)]
        $v struct $name(core::num::NonZeroU32);

        impl $name {
            /// Returns a handle that is guaranteed to always be invalid.
            #[allow(dead_code)]
            $v const fn null() -> Self {
                unsafe { $name(core::num::NonZeroU32::new_unchecked(
                    <Self as $crate::pool::Handle>::MAX_INDEX as u32
                )) }
            }
        }

        unsafe impl $crate::pool::Handle for $name {
            type Index = u16;
            const MAX_INDEX: usize = !(!0 << $n);
            const MAX_GENERATION: u32 = !(!0 << (32 - $n)) as u32;
            unsafe fn new(index: usize, generation: u32) -> Self {
                debug_assert!(index <= Self::MAX_INDEX);
                debug_assert!(generation <= Self::MAX_GENERATION);
                debug_assert_eq!(generation % 2, 1);
                let assembled = index as u32 & (Self::MAX_INDEX as u32) | ((generation as u32) << $n);
                $name(core::num::NonZeroU32::new_unchecked(assembled))
            }
            fn into_raw_parts(self) -> (usize, u32) {
                let raw: u32 = self.0.into();
                let index = (raw & (Self::MAX_INDEX as u32)) as usize;
                let generation = (raw >> $n) as u32;
                (index, generation)
            }
        }

        handle_type!($($rest)*);

    };
    () => {}
}

handle_type! {
    /// The default pool handle type, with 32 bits each for the index and generation count.
    pub DefaultHandle: 64;
}
