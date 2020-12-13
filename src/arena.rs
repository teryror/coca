//! Arena-based memory management.
//!
//! An arena controls a contiguous region of memory, partitioning it by simply
//! incrementing a pointer. Once such an allocation goes out of scope, the
//! memory cannot be reused until the entire region is cleared in aggregate.
//! This scheme has minimal runtime overhead, at the cost of internal memory
//! fragmentation.
//!
//! In order to guarantee safety, [`Arena`] cannot implement a `clear` method.
//! Instead, the underlying region is reset by dropping the arena, and may then
//! be freed or reused safely; you'll get an error if a [`Box<'_, T>`](Box)
//! pointing into it still lives. So this won't compile:
//!
//! ```compile_fail
//! use core::mem::MaybeUninit;
//! use coca::{Arena, Box};
//!
//! let bad_array = {
//!     let mut backing_region = [MaybeUninit::uninit(); 256];
//!     let mut arena = Arena::from(&mut backing_region[..]);
//!     arena.array_default::<i32>(10)
//! };
//! ```
//!
//! This makes it wasteful to mix long-lived allocations with short-lived ones
//! in the same arena. One solution is to [construct a temporary sub-arena][sub]
//! using the remaining memory. Sub-arenas may be nested arbitrarily, resulting
//! in stack-like behavior, which is sufficient for many allocation patterns.
//!
//! [sub]: Arena::make_sub_arena
//!
//! Note that this is legal but **strongly discouraged**:
//!
//! ```no_run
//! # use core::mem::MaybeUninit;
//! # use coca::{Arena, Box};
//! // callers must drop the return value before they can allocate from `arena` again!
//! fn semi_bad_array<'a>(arena: &'a mut Arena) -> Box<'a, [i32]> {
//!     let mut sub = arena.make_sub_arena();
//!     sub.array_default(10)
//! }
//! ```
//!
//! A `Box` should not outlive the arena it was allocated from. If temporary
//! allocations are required where an arena allocated value is to be returned,
//! consider using [`Arena::try_reserve`].
//!
//! # Memory Profiling
//! During development, it is common practice to provide arenas with more
//! memory than is assumed necessary, and track their peak utilization to
//! aid in determining a more appropriate size for deployment.
//!
//! To accomodate this, the `profile` feature enables the [`Arena::utilization`]
//! method and its return type, [`UtilizationProfile`]. Note that this requires
//! an allocation for some meta data when creating an arena from a buffer, which
//! may panic on buffers smaller than 40 bytes (the exact threshold depends on
//! your target platform's pointer size and the alignment of the passed buffer).
//! This does not apply to creating sub-arenas.

use crate::binary_heap::ArenaHeap;
use crate::storage::Capacity;
use crate::vec::ArenaVec;

use core::alloc::Layout;
use core::cmp::Ordering;
use core::fmt::{self, Debug, Display, Formatter, Pointer, Write};
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut, Range};
use core::ptr::{null_mut, slice_from_raw_parts_mut, NonNull};
use core::slice::from_raw_parts_mut;

/// A pointer type providing ownership of an arena allocation.
///
/// While the owned value will be dropped as normal, no additional overhead
/// for memory management is incurred.
///
/// See the [module-level documentation](crate::arena) for more.
pub struct Box<'src, T: ?Sized> {
    ptr: NonNull<T>,
    val: PhantomData<T>,        // Indicates this is an owning pointer
    src: PhantomData<&'src ()>, // Indicates this pointer must not outlive 'src
}

impl<'src, T: Sized> Box<'src, MaybeUninit<T>> {
    /// Converts `self` into a pointer to T.
    ///
    /// # Safety
    /// It is up to the caller to guarantee that the `MaybeUninit<T>` really is
    /// in an initialized state. Calling this when the content is not yet fully
    /// initialized causes undefined behavior.
    ///
    /// See the type-level documentation on [`MaybeUninit`] for more information
    /// about this initialization invariant.
    #[inline]
    pub unsafe fn assume_init(mut self) -> Box<'src, T> {
        let ptr = self.as_mut_ptr();
        core::mem::forget(self);

        Box {
            ptr: NonNull::new_unchecked(ptr),
            val: PhantomData,
            src: PhantomData,
        }
    }

    /// Places `x` into the allocation and converts `self` into a pointer to T.
    ///
    /// See [`Arena::try_reserve`] for example usage.
    #[inline]
    pub fn init(mut self, x: T) -> Box<'src, T> {
        let ptr = self.as_mut_ptr();

        unsafe {
            ptr.write(x);
            self.assume_init()
        }
    }
}

impl<'src, T: Sized> Box<'src, [MaybeUninit<T>]> {
    /// Converts `self` into a pointer to \[T\].
    ///
    /// # Safety
    /// It is up to the caller to guarantee that each `MaybeUninit<T>` in the
    /// slice really is in an initialized state. Calling this when the content
    /// is not yet fully initialized causes undefined behavior.
    ///
    /// See the type-level documentation on [`MaybeUninit`] for more information
    /// about this initialization invariant.
    #[inline]
    pub unsafe fn assume_init(mut self) -> Box<'src, [T]> {
        let ptr = self.as_mut_ptr() as *mut T;
        let len = self.len();
        core::mem::forget(self);

        Box {
            ptr: NonNull::new_unchecked(slice_from_raw_parts_mut(ptr, len)),
            val: PhantomData,
            src: PhantomData,
        }
    }

    /// Calls `f` once with each index into `self`, placing the returned value
    /// at that position, and then converts `self` into a pointer to \[T\].
    ///
    /// See [`Arena::try_reserve_array`] for example usage.
    #[inline]
    pub fn init_with<F: Fn(usize) -> T>(mut self, f: F) -> Box<'src, [T]> {
        unsafe {
            for i in 0..self.len() {
                self[i].as_mut_ptr().write(f(i));
            }

            self.assume_init()
        }
    }
}

impl<T: ?Sized> Deref for Box<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T: ?Sized> DerefMut for Box<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T: ?Sized> AsRef<T> for Box<'_, T> {
    fn as_ref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T: ?Sized> AsMut<T> for Box<'_, T> {
    fn as_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T: ?Sized> Drop for Box<'_, T> {
    fn drop(&mut self) {
        // TODO: Verify that calls to this function are optimized out when T: !Drop
        unsafe { self.ptr.as_ptr().drop_in_place() }
    }
}

impl<T: Debug + ?Sized> Debug for Box<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&**self, f)
    }
}

impl<T: Display + ?Sized> Display for Box<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&**self, f)
    }
}

impl<T: ?Sized> Pointer for Box<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Pointer::fmt(&self.ptr, f)
    }
}

impl<T: ?Sized + PartialEq> PartialEq for Box<'_, T> {
    #[inline]
    fn eq(&self, other: &Box<'_, T>) -> bool {
        PartialEq::eq(&**self, &**other)
    }
}
impl<T: ?Sized + PartialOrd> PartialOrd for Box<'_, T> {
    #[inline]
    fn partial_cmp(&self, other: &Box<'_, T>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
    #[inline]
    fn lt(&self, other: &Box<'_, T>) -> bool {
        PartialOrd::lt(&**self, &**other)
    }
    #[inline]
    fn le(&self, other: &Box<'_, T>) -> bool {
        PartialOrd::le(&**self, &**other)
    }
    #[inline]
    fn ge(&self, other: &Box<'_, T>) -> bool {
        PartialOrd::ge(&**self, &**other)
    }
    #[inline]
    fn gt(&self, other: &Box<'_, T>) -> bool {
        PartialOrd::gt(&**self, &**other)
    }
}

impl<T: ?Sized + Ord> Ord for Box<'_, T> {
    #[inline]
    fn cmp(&self, other: &Box<T>) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

impl<T: ?Sized + Eq> Eq for Box<'_, T> {}

impl<T: ?Sized + Hash> Hash for Box<'_, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<T: ?Sized + Hasher> Hasher for Box<'_, T> {
    fn finish(&self) -> u64 {
        (**self).finish()
    }
    fn write(&mut self, bytes: &[u8]) {
        (**self).write(bytes)
    }
    fn write_u8(&mut self, i: u8) {
        (**self).write_u8(i)
    }
    fn write_u16(&mut self, i: u16) {
        (**self).write_u16(i)
    }
    fn write_u32(&mut self, i: u32) {
        (**self).write_u32(i)
    }
    fn write_u64(&mut self, i: u64) {
        (**self).write_u64(i)
    }
    fn write_u128(&mut self, i: u128) {
        (**self).write_u128(i)
    }
    fn write_usize(&mut self, i: usize) {
        (**self).write_usize(i)
    }
    fn write_i8(&mut self, i: i8) {
        (**self).write_i8(i)
    }
    fn write_i16(&mut self, i: i16) {
        (**self).write_i16(i)
    }
    fn write_i32(&mut self, i: i32) {
        (**self).write_i32(i)
    }
    fn write_i64(&mut self, i: i64) {
        (**self).write_i64(i)
    }
    fn write_i128(&mut self, i: i128) {
        (**self).write_i128(i)
    }
    fn write_isize(&mut self, i: isize) {
        (**self).write_isize(i)
    }
}

impl<I: Iterator + ?Sized> Iterator for Box<'_, I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        (**self).next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (**self).size_hint()
    }
    fn nth(&mut self, n: usize) -> Option<I::Item> {
        (**self).nth(n)
    }
}

#[cfg(feature = "profile")]
#[derive(Copy, Clone)]
struct ProfileMetaData {
    initial_cursor_pos: usize,
    peak_cursor_pos: usize,
    allocation_count: usize,
    failed_allocations: usize,
}

/// A summary of all allocations from an arena and all its sub-arenas from it
/// since its creation.
///
/// Note that every call to `ArenaWrite::write_str` individually counts towards
/// `allocation_count` and, if unsuccessful, `failed_allocations`, so strings
/// created with [`fmt!`] are counted as multiple allocations.
#[cfg(feature = "profile")]
#[cfg_attr(docs_rs, doc(cfg(feature = "profile")))]
#[derive(Copy, Clone, Debug)]
pub struct UtilizationProfile {
    /// The maximum number of occupied bytes at any point in time, including padding.
    pub peak_utilization: usize,
    /// The total number of allocations attempted, including failed allocations.
    pub allocation_count: usize,
    /// The total number of attempted allocations for which the remaining space
    /// was insufficient.
    pub failed_allocations: usize,
}

/// A memory arena, also known as a region-based allocator, or bump allocator.
///
/// See the the [module-level documentation](crate::arena) for more.
pub struct Arena<'src> {
    cursor: *mut MaybeUninit<u8>,
    end: *mut MaybeUninit<u8>,
    src: PhantomData<&'src mut ()>, // Ensures you can't allocate out of the source arena while this one is still alive
}

impl<'src> From<&'src mut [MaybeUninit<u8>]> for Arena<'src> {
    /// Constructs a new `Arena` allocating out of `buf`.
    ///
    /// # Panics
    /// When compiled with the `profile` feature, panics if `buf` is too small
    /// to fit the profiling meta data. The exact threshold depends on the size
    /// of `usize` on the target platform, and the alignment of `buf`, but this
    /// is guaranteed to succeed if `buf.len() >= 40`.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let arena = Arena::from(&mut backing_region[..]);
    /// ```
    #[inline]
    fn from(buf: &mut [MaybeUninit<u8>]) -> Self {
        let Range { start, end } = buf.as_mut_ptr_range();

        #[cfg(feature = "profile")]
        let end = {
            use core::mem::size_of;

            let layout = Layout::new::<ProfileMetaData>();
            let align_offset = end.align_offset(layout.align());
            assert!(align_offset < size_of::<usize>());

            let end_of_meta = end
                .wrapping_add(align_offset)
                .wrapping_sub(size_of::<usize>());
            let new_end = end_of_meta.wrapping_sub(layout.size());
            assert!(start <= new_end);
            assert!(new_end < end_of_meta);
            assert!(end_of_meta <= end);

            let meta = new_end as *mut ProfileMetaData;
            unsafe {
                meta.write(ProfileMetaData {
                    initial_cursor_pos: start as usize,
                    peak_cursor_pos: start as usize,
                    allocation_count: 0,
                    failed_allocations: 0,
                });
            }

            new_end
        };

        Arena {
            cursor: start,
            end,
            src: PhantomData,
        }
    }
}

impl Debug for Arena<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        core::write!(f, "Arena({:p}..{:p})", self.cursor, self.end)
    }
}

impl<'src> Arena<'src> {
    /// Calculates the size of the space remaining in the arena in bytes.
    ///
    /// An allocation is not guaranteed to succeed even when the returned value
    /// is greater than or equal to the requested number of bytes, because
    /// proper alignment may require additional padding. Use the `try_` methods
    /// to handle allocation failure.
    #[inline]
    pub fn bytes_remaining(&self) -> usize {
        (self.end as usize) - (self.cursor as usize)
    }

    /// Constructs a new `Arena` allocating out of the free space remaining in `self`.
    /// `self` cannot be used for allocation until the new arena is dropped.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from(&mut backing_region[..]);
    ///
    /// {
    ///     let mut tmp = arena.make_sub_arena();
    ///     let arr = tmp.alloc([0u32; 200]);              // this takes up 800 / 1024 bytes...
    ///     assert!(tmp.try_alloc([0u32; 100]).is_none()); // ...so this can't succeed
    /// }
    ///
    /// // tmp was dropped, so the memory can be reused:
    /// assert!(arena.try_alloc([0u32; 200]).is_some());
    /// ```
    #[inline]
    pub fn make_sub_arena(&mut self) -> Arena<'_> {
        Arena {
            cursor: self.cursor,
            end: self.end,
            src: PhantomData,
        }
    }

    #[inline]
    fn try_alloc_raw(&mut self, alloc_layout: &Layout) -> *mut MaybeUninit<u8> {
        let align_offset = self.cursor.align_offset(alloc_layout.align());

        // `ptr::align_offset()` returns `usize::MAX` when aligning the pointer
        // isn't possible, which shouldn't ever happen with a `*u8`, BUT:
        // the implementation is free to _always_ return `usize::MAX`, so
        // we'll leave getting rid of this check to the optimizer
        assert!(align_offset != usize::MAX);

        #[cfg(feature = "profile")]
        {
            self.profile_meta_data_mut().allocation_count += 1;
        }

        // we can't eagerly compute `result` and `new_cursor`, because it's UB
        // for the result of `ptr::add` to be out of bounds, so the correct way
        // to check bounds here is through usize arithmetic:
        if let Some(total_bytes) = align_offset.checked_add(alloc_layout.size()) {
            if self.bytes_remaining() >= total_bytes {
                let result = unsafe { self.cursor.add(align_offset) };
                let new_cursor = unsafe { result.add(alloc_layout.size()) };
                self.cursor = new_cursor;

                #[cfg(feature = "profile")]
                {
                    let meta = self.profile_meta_data_mut();
                    if meta.peak_cursor_pos < new_cursor as usize {
                        meta.peak_cursor_pos = new_cursor as usize;
                    }
                }

                return result;
            }
        }

        #[cfg(feature = "profile")]
        {
            self.profile_meta_data_mut().failed_allocations += 1;
        }

        null_mut()
    }

    /// Allocates memory in the arena and then places the `Default` value for T
    /// into it.
    ///
    /// # Panics
    /// Panics if the remaining space in the arena is insufficient. See
    /// [`try_alloc_default`](Arena::try_alloc_default) for a checked version
    /// that never panics.
    #[inline]
    #[track_caller]
    pub fn alloc_default<T: Default + Sized>(&mut self) -> Box<'src, T> {
        self.try_reserve()
            .expect("unexpected allocation failure in `alloc_default`")
            .init(T::default())
    }

    /// Allocates memory in the arena and then places the `Default` value for T
    /// into it.
    ///
    /// Returns [`None`] if the remaining space in the arena is insufficient.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// # fn test() -> Option<()> {
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from(&mut backing_region[..]);
    ///
    /// loop {
    ///     if let Some(ptr) = arena.try_alloc_default::<u128>() {
    ///         assert_eq!(*ptr, 0);
    ///     } else {
    ///         break;
    ///     }
    /// }
    ///
    /// assert!(arena.bytes_remaining() < 32);
    /// # Some(())
    /// # }
    /// # assert!(test().is_some());
    /// ```
    #[inline]
    pub fn try_alloc_default<T: Default + Sized>(&mut self) -> Option<Box<'src, T>> {
        self.try_reserve().map(|b| b.init(T::default()))
    }

    /// Allocates memory in the arena and then places `x` into it.
    ///
    /// # Panics
    /// Panics if the remaining space in the arena is insufficient. See
    /// [`try_alloc`](Arena::try_alloc) for a checked version that never panics.
    #[inline]
    #[track_caller]
    pub fn alloc<T: Sized>(&mut self, x: T) -> Box<'src, T> {
        self.try_reserve()
            .expect("unexpected allocation failure in `alloc`")
            .init(x)
    }

    /// Allocates memory in the arena and then places `x` into it.
    ///
    /// Returns [`None`] if the remaining space in the arena is insufficient.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// # fn test() -> Option<()> {
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from(&mut backing_region[..]);
    ///
    /// loop {
    ///     if let Some(ptr) = arena.try_alloc(0xDEAD_BEEFu32) {
    ///         assert_eq!(*ptr, 0xDEAD_BEEF);
    ///     } else {
    ///         break;
    ///     }
    /// }
    ///
    /// assert!(arena.bytes_remaining() < 8);
    /// # Some(())
    /// # }
    /// # assert!(test().is_some());
    /// ```
    #[inline]
    pub fn try_alloc<T: Sized>(&mut self, x: T) -> Option<Box<'src, T>> {
        self.try_reserve().map(|b| b.init(x))
    }

    /// Allocates memory in the arena, leaving it uninitialized.
    ///
    /// # Panics
    /// Panics if the remaining space in the arena is insufficient. See
    /// [`try_reserve`](Arena::try_reserve) for a checked version that never panics.
    #[inline]
    #[track_caller]
    pub fn reserve<T: Sized>(&mut self) -> Box<'src, MaybeUninit<T>> {
        self.try_reserve()
            .expect("unexpected allocation failure in `reserve`")
    }

    /// Allocates memory in the arena, leaving it uninitialized.
    ///
    /// Returns [`None`] if the remaining space in the arena is insufficient.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// # fn test() -> Option<()> {
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from(&mut backing_region[..]);
    ///
    /// let total = {
    ///     let reserved = arena.try_reserve::<i32>()?;
    ///     let mut tmp = arena.make_sub_arena();
    ///     let a = tmp.alloc(5);
    ///     let b = tmp.alloc(7);
    ///     reserved.init(*a + *b)
    /// };
    ///
    /// assert_eq!(*total, 12);
    /// # Some(())
    /// # }
    /// # assert!(test().is_some());
    /// ```
    #[inline]
    pub fn try_reserve<T: Sized>(&mut self) -> Option<Box<'src, MaybeUninit<T>>> {
        let ptr = self.try_alloc_raw(&Layout::new::<T>()) as *mut MaybeUninit<T>;
        if ptr.is_null() {
            return None;
        }

        Some(Box {
            ptr: unsafe { NonNull::new_unchecked(ptr) },
            val: PhantomData,
            src: PhantomData,
        })
    }

    /// Allocates memory in the arena, leaving it uninitialized.
    ///
    /// # Panics
    /// Panics if the remaining space in the arena is insufficient. See
    /// [`try_reserve_array`](Arena::try_reserve_array) for a checked version
    /// that never panics.
    #[inline]
    #[track_caller]
    pub fn reserve_array<T: Sized>(&mut self, count: usize) -> Box<'src, [MaybeUninit<T>]> {
        self.try_reserve_array(count)
            .expect("unexpected allocation failure in `reserve_array`")
    }

    /// Allocates memory in the arena, leaving it uninitialized.
    ///
    /// Returns [`None`] if the remaining space in the arena is insufficient.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// # fn test() -> Option<()> {
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from(&mut backing_region[..]);
    ///
    /// let sums = arena
    ///     .try_reserve_array::<usize>(100)?
    ///     .init_with(|n| (n * (n + 1)) / 2);
    /// assert!(arena.try_reserve_array::<usize>(100).is_none());
    ///
    /// assert_eq!(&sums[..10], [0, 1, 3, 6, 10, 15, 21, 28, 36, 45]);
    /// assert_eq!(sums.last(), Some(&4950));
    /// # Some(())
    /// # }
    /// # assert!(test().is_some());
    /// ```
    #[inline]
    pub fn try_reserve_array<T: Sized>(
        &mut self,
        count: usize,
    ) -> Option<Box<'src, [MaybeUninit<T>]>> {
        let ptr = self.try_array_raw(count);
        if ptr.is_null() {
            return None;
        }

        Some(Box {
            ptr: unsafe { NonNull::new_unchecked(ptr) },
            val: PhantomData,
            src: PhantomData,
        })
    }

    /// Allocates memory in the arena and then places `count` copies of the
    /// `Default` value for T into it.
    ///
    /// Consider using [`alloc_default<[T; count]>`](Arena::alloc_default)
    /// instead when `count` is known at compile time.
    ///
    /// # Panics
    /// Panics if the remaining space in the arena is insufficient.
    /// See [`try_array_default`](Arena::try_array_default) for a checked
    /// version that never panics.
    #[inline]
    #[track_caller]
    pub fn array_default<T>(&mut self, count: usize) -> Box<'src, [T]>
    where
        T: Default + Sized,
    {
        self.try_reserve_array(count)
            .expect("unexpected allocation failure in `array_default`")
            .init_with(|_| T::default())
    }

    /// Allocates memory in the arena and then places `count` copies of the
    /// `Default` value for T into it.
    ///
    /// Returns [`None`] if the remaining space in the arena is insufficient.
    ///
    /// Consider using [`try_alloc_default<[T; count]>`](Arena::try_alloc_default)
    /// instead when `count` is known at compile time.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// # fn test() -> Option<()> {
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from(&mut backing_region[..]);
    /// let array = arena.try_array_default::<u128>(16)?;
    /// assert_eq!(&array[..], &[0; 16]);
    /// # Some(())
    /// # }
    /// # assert!(test().is_some());
    /// ```
    #[inline]
    pub fn try_array_default<T>(&mut self, count: usize) -> Option<Box<'src, [T]>>
    where
        T: Default + Sized,
    {
        self.try_reserve_array(count)
            .map(|b| b.init_with(|_| T::default()))
    }

    /// Allocates memory in the arena and then places `count` copies of `x`
    /// into it.
    ///
    /// Consider using [`alloc([x; count])`](Arena::alloc) instead when `count`
    /// is known at compile time.
    ///
    /// # Panics
    /// Panics if the remaining space in the arena is insufficient.
    /// See [`try_array`](Arena::try_array) for a checked version that never panics.
    #[inline]
    #[track_caller]
    pub fn array<T>(&mut self, x: T, count: usize) -> Box<'src, [T]>
    where
        T: Copy + Sized,
    {
        self.try_reserve_array(count)
            .expect("unexpected allocation failure in `array`")
            .init_with(|_| x)
    }

    #[inline]
    fn try_array_raw<T>(&mut self, count: usize) -> *mut [MaybeUninit<T>]
    where
        T: Sized,
    {
        let alloc_layout = match Layout::array::<T>(count) {
            Ok(layout) => layout,
            Err(_) => {
                return slice_from_raw_parts_mut(null_mut(), 0);
            }
        };

        let ptr = self.try_alloc_raw(&alloc_layout) as *mut MaybeUninit<T>;
        if ptr.is_null() {
            return slice_from_raw_parts_mut(null_mut(), 0);
        }

        slice_from_raw_parts_mut(ptr, count)
    }

    /// Allocates memory in the arena and then places `count` copies of `x`
    /// into it.
    ///
    /// Returns [`None`] if the remaining space in the arena is insufficient.
    ///
    /// Consider using [`try_alloc([x; count])`](Arena::try_alloc) instead when
    /// `count` is known at compile time.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// # fn test() -> Option<()> {
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from(&mut backing_region[..]);
    /// let array = arena.try_array(0x12345678u32, 200)?;
    /// assert_eq!(&array[..], &[0x12345678u32; 200]);
    /// # Some(())
    /// # }
    /// # assert!(test().is_some());
    /// ```
    #[inline]
    pub fn try_array<T>(&mut self, x: T, count: usize) -> Option<Box<'src, [T]>>
    where
        T: Copy + Sized,
    {
        self.try_reserve_array(count).map(|b| b.init_with(|_| x))
    }

    /// Constructs a [`ArenaVec`] with the given capacity.
    ///
    /// # Panics
    /// Panics if the specified capacity cannot be represented by a `usize`, or
    /// if the remaining space in the arena is insufficient. See
    /// [`try_vec`](Arena::try_vec) for a checked version.
    #[track_caller]
    pub fn vec<T, I: Capacity>(&mut self, capacity: I) -> ArenaVec<'src, T, I> {
        self.try_vec(capacity)
            .expect("unexpected allocation failure in `vec`")
    }

    /// Constructs an [`ArenaVec`] with the given capacity.
    ///
    /// Returns [`None`] if the remaining space in the arena is insufficient.
    ///
    /// # Panics
    /// Panics if the specified capacity cannot be represented by a `usize`.
    ///
    /// # Examples
    /// ```
    /// use coca::Arena;
    /// use core::mem::MaybeUninit;
    ///
    /// # fn test() -> Option<()> {
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from(&mut backing_region[..]);
    ///
    /// let mut squares = arena.try_vec::<i64, usize>(100)?;
    /// assert!(arena.try_vec::<i64, usize>(100).is_none());
    ///
    /// assert_eq!(squares.len(), 0);
    /// assert_eq!(squares.capacity(), 100);
    ///
    /// for x in 1..=100 { squares.push(x * x) }
    /// assert_eq!(&squares[..8], &[1, 4, 9, 16, 25, 36, 49, 64]);
    /// # Some(())
    /// # }
    /// # assert!(test().is_some());
    /// ```
    pub fn try_vec<T, I: Capacity>(&mut self, capacity: I) -> Option<ArenaVec<'src, T, I>> {
        Some(ArenaVec::<T, I>::from(
            self.try_reserve_array(capacity.into_usize())?,
        ))
    }

    /// Constructs a [`ArenaHeap`] with the given capacity.
    ///
    /// # Panics
    /// Panics if the specified capacity cannot be represented by a `usize`, or
    /// if the remaining space in the arena is insufficient. See
    /// [`try_heap`](Arena::try_heap) for a checked version.
    #[track_caller]
    pub fn heap<T: Ord, I: Capacity>(&mut self, capacity: I) -> ArenaHeap<'src, T, I> {
        self.try_heap(capacity)
            .expect("unexpected allocation failure in `heap`")
    }

    /// Constructs an [`ArenaHeap`] with the given capacity.
    ///
    /// Returns [`None`] if the remaining space in the arena is insufficient.
    ///
    /// # Panics
    /// Panics if the specified capacity cannot be represented by a `usize`.
    ///
    /// # Examples
    /// ```
    /// use coca::Arena;
    /// use core::mem::MaybeUninit;
    ///
    /// # fn test() -> Option<()> {
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from(&mut backing_region[..]);
    ///
    /// let mut heap = arena.try_heap::<i64, usize>(100)?;
    /// assert!(arena.try_heap::<i64, usize>(100).is_none());
    ///
    /// assert_eq!(heap.len(), 0);
    /// assert_eq!(heap.capacity(), 100);
    ///
    /// for x in 1..=100 { heap.push(x) }
    /// for x in (1..=100).rev() {
    ///     assert_eq!(heap.pop(), Some(x));
    /// }
    /// # Some(())
    /// # }
    /// # assert!(test().is_some());
    /// ```
    pub fn try_heap<T: Ord, I: Capacity>(&mut self, capacity: I) -> Option<ArenaHeap<'src, T, I>> {
        Some(ArenaHeap::from(
            self.try_reserve_array(capacity.into_usize())?,
        ))
    }

    /// Transforms an iterator into a boxed slice in the arena.
    ///
    /// # Panics
    /// Panics if the remaining space in the arena is insufficient to exhaust
    /// the iterator. See [`try_collect`](Arena::try_collect) for a checked
    /// version that never panics.
    #[inline]
    #[track_caller]
    pub fn collect<T, I>(&mut self, iter: I) -> Box<'src, [T]>
    where
        T: Sized,
        I: IntoIterator<Item = T>,
    {
        self.try_collect(iter)
            .expect("unexpected allocation failure in `collect`")
    }

    /// Transforms an iterator into a boxed slice in the arena.
    ///
    /// Returns [`None`] if the remaining space in the arena is insufficient
    /// to exhaust the iterator.
    ///
    /// # Examples
    /// ```
    /// use core::mem::{MaybeUninit, size_of, size_of_val};
    /// use coca::Arena;
    ///
    /// # fn test() -> Option<()> {
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from(&mut backing_region[..]);
    ///
    /// let a = [1, 2, 3];
    /// let doubled = arena.try_collect(a.iter().map(|&x| x * 2))?;
    ///
    /// assert_eq!(&doubled[..], &[2, 4, 6]);
    /// # Some(())
    /// # }
    /// # assert!(test().is_some());
    /// ```
    pub fn try_collect<T, I>(&mut self, iter: I) -> Option<Box<'src, [T]>>
    where
        T: Sized,
        I: IntoIterator<Item = T>,
    {
        let alloc_layout = Layout::new::<T>();
        let align_offset = self.cursor.align_offset(alloc_layout.align());
        assert!(align_offset != usize::MAX);

        #[cfg(feature = "profile")]
        {
            self.profile_meta_data_mut().allocation_count += 1;
        }

        let bytes_remaining = self.bytes_remaining();
        if bytes_remaining < align_offset {
            #[cfg(feature = "profile")]
            {
                self.profile_meta_data_mut().failed_allocations += 1;
            }
            return None;
        }

        let item_capacity = (bytes_remaining - align_offset) / core::mem::size_of::<T>();

        let base = unsafe { self.cursor.add(align_offset) as *mut T };
        let mut count = 0usize;
        let mut cursor = base;

        for val in iter {
            if count == item_capacity {
                for i in 0..count {
                    unsafe {
                        base.add(i).drop_in_place();
                    }
                }

                #[cfg(feature = "profile")]
                {
                    self.profile_meta_data_mut().failed_allocations += 1;
                }

                return None;
            }

            count += 1;
            unsafe {
                cursor.write(val);
                cursor = cursor.add(1);
            }
        }

        self.cursor = cursor as *mut MaybeUninit<u8>;

        #[cfg(feature = "profile")]
        {
            let meta = self.profile_meta_data_mut();
            if meta.peak_cursor_pos < cursor as usize {
                meta.peak_cursor_pos = cursor as usize;
            }
        }

        unsafe {
            let slice = from_raw_parts_mut(base, count);
            Some(Box {
                ptr: NonNull::new_unchecked(slice),
                val: PhantomData,
                src: PhantomData,
            })
        }
    }

    /// Constructs a new [`ArenaWriter`] backed by the free space remaining in `self`.
    ///
    /// The arena cannot be used for allocation until the writer is dropped.
    ///
    /// Primarily intended for use in expansions of [`fmt!`]. This should only
    /// be used explicitly where format strings don't work as well.
    ///
    /// # Examples
    /// ```
    /// use coca::{Arena, Box};
    /// use core::{fmt::Write, mem::MaybeUninit};
    ///
    /// # fn main() -> Result<(), core::fmt::Error> {
    /// let parts = ["Hello", ",", " ", "World", "!"];
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from(&mut backing_region[..]);
    ///
    /// let mut writer = arena.make_writer();
    /// for s in parts.iter() {
    ///     writer.write_str(s)?;
    /// }
    ///
    /// let combined: Box::<'_, str> = writer.into();
    /// assert_eq!(combined.as_ref(), "Hello, World!");
    /// # Ok(())
    /// # }
    #[inline]
    pub fn make_writer<'a>(&'a mut self) -> ArenaWriter<'a, 'src> {
        ArenaWriter {
            source: self,
            len: 0,
        }
    }
}

#[cfg(feature = "profile")]
impl Arena<'_> {
    /// Returns a profile of all allocations from the arena and all sub-arenas created from it.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// let mut backing_region = [MaybeUninit::uninit(); 256];
    /// let mut arena = Arena::from(&mut backing_region[..]);
    ///
    /// {
    ///     let mut tmp = arena.make_sub_arena();
    ///     let _ = tmp.array_default::<u8>(100);
    /// }
    /// {
    ///     let mut tmp = arena.make_sub_arena();
    ///     let _ = tmp.array_default::<u8>(50);
    ///     let _ = tmp.try_array_default::<u8>(200);
    /// }
    /// {
    ///     let mut tmp = arena.make_sub_arena();
    ///     let _ = tmp.array_default::<u8>(200);
    /// }
    ///
    /// let profile = arena.utilization();
    /// assert_eq!(profile.peak_utilization, 200);
    /// assert_eq!(profile.allocation_count, 4);
    /// assert_eq!(profile.failed_allocations, 1);
    /// ```
    #[inline]
    pub fn utilization(&self) -> UtilizationProfile {
        let &ProfileMetaData {
            initial_cursor_pos,
            peak_cursor_pos,
            allocation_count,
            failed_allocations,
        } = unsafe { (self.end as *const ProfileMetaData).as_ref().unwrap() };
        UtilizationProfile {
            peak_utilization: peak_cursor_pos - initial_cursor_pos,
            allocation_count,
            failed_allocations,
        }
    }

    #[inline]
    fn profile_meta_data_mut(&mut self) -> &mut ProfileMetaData {
        unsafe { (self.end as *mut ProfileMetaData).as_mut().unwrap() }
    }
}

/// Implementor of [`core::fmt::Write`] backed by an [`Arena`].
/// Primarily intended for use in expansions of [`fmt!`].
///
/// See [`Arena::make_writer`] for example usage.
pub struct ArenaWriter<'src, 'buf> {
    source: &'src mut Arena<'buf>,
    len: usize,
}

impl Write for ArenaWriter<'_, '_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let bytes_remaining = self.source.bytes_remaining();
        if s.len() > bytes_remaining {
            #[cfg(feature = "profile")]
            {
                self.source.profile_meta_data_mut().allocation_count += 1;
                self.source.profile_meta_data_mut().failed_allocations += 1;
            }
            return fmt::Result::Err(fmt::Error);
        }

        unsafe {
            s.as_ptr()
                .copy_to_nonoverlapping(self.source.cursor as *mut u8, s.len());
        }

        self.source.cursor = unsafe { self.source.cursor.add(s.len()) };
        self.len += s.len();

        #[cfg(feature = "profile")]
        {
            let cursor = self.source.cursor as usize;
            let meta = self.source.profile_meta_data_mut();

            meta.allocation_count += 1;
            if meta.peak_cursor_pos < cursor {
                meta.peak_cursor_pos = cursor;
            }
        }

        Ok(())
    }
}

impl<'buf> From<ArenaWriter<'_, 'buf>> for Box<'buf, str> {
    fn from(writer: ArenaWriter<'_, 'buf>) -> Self {
        unsafe {
            let ptr = writer.source.cursor.sub(writer.len) as *mut u8;
            let slice = from_raw_parts_mut(ptr, writer.len);
            let str_ptr = NonNull::new_unchecked(slice).as_ptr() as *mut str;

            Box {
                ptr: NonNull::new_unchecked(str_ptr),
                val: PhantomData,
                src: PhantomData,
            }
        }
    }
}

/// Creates a `Option<Box<'_, str>>` using interpolation of runtime expressions.
///
/// The first argument `fmt!` receives is an [`Arena`] from which the string
/// will be allocated.
///
/// The second argument is a format string. This must be a string literal.
/// Additional parameters passed to `fmt!` replace the `{}`s contained within
/// the formatting string in the order given unless named or positional
/// parameters are used; see [`core::fmt`] for more information.
///
/// Evaluates to `None` if the arena does not have enough space remaining to
/// contain the formatted string.
///
/// # Examples
/// ```
/// use coca::{Arena, fmt};
/// use core::mem::MaybeUninit;
///
/// # fn test() -> Option<()> {
/// let mut backing_region = [MaybeUninit::uninit(); 256];
/// let mut arena = Arena::from(&mut backing_region[..]);
/// let output = fmt!(arena, "test")?;
/// let output = fmt!(arena, "hello {}", "world!")?;
/// # Some(())
/// # }
/// # assert!(test().is_some());
/// ```
#[macro_export]
macro_rules! fmt {
    ($arena:expr, $($arg:tt)*) => {{
        use core::fmt::Write;
        let mut writer = $arena.make_writer();
        core::write!(writer, $($arg)*)
            .ok()
            .map(|_| $crate::Box::<'_, str>::from(writer))
    }}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn failed_collect_drops_taken_items() {
        use core::cell::Cell;
        struct Droppable<'a> {
            drop_count: &'a Cell<usize>,
        }

        impl Drop for Droppable<'_> {
            fn drop(&mut self) {
                let count = self.drop_count.get();
                self.drop_count.set(count + 1);
            }
        }

        const ARENA_SIZE: usize = 321;
        let mut backing_region = [MaybeUninit::uninit(); ARENA_SIZE];
        let mut arena = Arena::from(&mut backing_region[..]);

        let mut taken_count = 0;
        let drop_count = Cell::new(0);
        let result = arena.try_collect((0..100).map(|_| {
            taken_count += 1;
            Droppable {
                drop_count: &drop_count,
            }
        }));

        assert!(result.is_none());
        assert_eq!(taken_count, drop_count.get());

        let alloc_for_arena_size = arena.try_array_default::<u8>(ARENA_SIZE);
        if cfg!(feature = "profile") {
            // because of inserted metadata:
            assert!(alloc_for_arena_size.is_none());
        } else {
            assert!(alloc_for_arena_size.is_some());
        }
    }

    #[test]
    fn format_boxed_debug_struct() {
        let mut backing_region = [MaybeUninit::uninit(); 256];
        let mut arena = Arena::from(&mut backing_region[..]);

        #[derive(Debug)]
        struct LinkedList<'a> {
            val: i64,
            next: Option<Box<'a, LinkedList<'a>>>,
        }

        let a = arena.alloc(LinkedList { val: 0, next: None });
        let b = arena.alloc(LinkedList {
            val: 1,
            next: Some(a),
        });

        let output = fmt!(arena, "{:?}", b).unwrap();

        let _c = arena.alloc(LinkedList {
            val: 2,
            next: Some(b),
        });

        assert_eq!(
            output.as_ref(),
            "LinkedList { val: 1, next: Some(LinkedList { val: 0, next: None }) }"
        );
    }

    #[test]
    fn debug_impl() {
        let mut backing_region_a = [MaybeUninit::uninit(); 256];
        let mut arena_a = Arena::from(&mut backing_region_a[..]);

        let mut backing_region_b = [MaybeUninit::uninit(); 256];
        let arena_b = Arena::from(&mut backing_region_b[..]);

        let output = fmt!(arena_a, "{:?}", arena_b).unwrap();
        assert_eq!(&output[..8], "Arena(0x");

        let chars_per_ptr = (output.len() - 13) / 2;
        assert_eq!(&output[8 + chars_per_ptr..12 + chars_per_ptr], "..0x");
        assert_eq!(&output[12 + 2 * chars_per_ptr..], ")");
    }
}
