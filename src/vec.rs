//! Contiguous growable array types with constant capacity.
//!
//! Bounded vectors have O(1) indexing, push and pop (from the end), as well as
//! unordered removal.
//!
//! Unlike `alloc::Vec`, [`coca::Vec`](Vec) is not only generic over the element type,
//! but also the underlying storage mechanism and index type (which defaults to
//! `usize`).
//!
//! With no optional features enabled, the only supported storage types are
//! [references to slices](SliceVec), [arena-allocated slices](ArenaVec),
//! [arrays inlined in the `Vec`](InlineVec), as well as referenced and
//! (arena-)boxed arrays, which do not require a run-time representation of
//! their capacity.
//!
//! The `alloc` feature allows using [owned slices](AllocVec) for storage. Note
//! that such a vector still does not reallocate - this may be useful in cases
//! where domain logic dictates a length limit on a list.
//!
//! Specifying an index type smaller than `usize`, such as `u16` or even `u8`,
//! can aid in struct size optimization, especially with `InlineVec`. It's also
//! possible to [declare new types](index_type!) for this purpose, leveraging
//! the type system to avoid using the wrong kind of index.
//!
//! Because the capacity is constant, operations that grow the vector,
//! such as [`push`](Vec::push) and [`insert`](Vec::insert), may fail.
//! Checked versions of these methods are provided ([`try_push`](Vec::try_push),
//! [`try_insert`](Vec::try_insert)).
//!
//! ---
//!
//! Parts of the implementation and documentation of this module were adapted
//! from the Rust standard library Vec, and from `tinyvec::SliceVec` (Copyright
//! (c) 2019 by Daniel "Lokathor" Gee).

use crate::storage::InlineStorage;

use crate::storage::{
    buffer_too_large_for_index_type, mut_ptr_at_index, normalize_range, ptr_at_index, ArrayLike, Capacity, Storage,
};

use core::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};
use core::hash::{Hash, Hasher};
use core::iter::{DoubleEndedIterator, FusedIterator, IntoIterator as IntoIter, Iterator};
use core::marker::PhantomData;
#[allow(unused_imports)] // used only when some features are enabled
use core::mem::MaybeUninit;
use core::ops::{Range, RangeBounds};
use core::ptr;

/// A contiguous growable array type with constant capacity.
///
/// Generic over the storage buffer type `S` and the index type `I`.
///
/// See the [module-level documentation](crate::vec) for more.
pub struct Vec<T, S: Storage<ArrayLike<T>>, I: Capacity = usize> {
    len: I,
    buf: S,
    elem: PhantomData<T>,
}

/// A vector using any mutable slice for storage.
///
/// # Examples
/// ```
/// use core::mem::MaybeUninit;
/// let mut backing_array = [MaybeUninit::<char>::uninit(); 32];
/// let (slice1, slice2) = (&mut backing_array[..]).split_at_mut(16);
/// let mut vec1 = coca::SliceVec::<_>::from(slice1);
/// let mut vec2 = coca::SliceVec::<_>::from(slice2);
/// assert_eq!(vec1.capacity(), 16);
/// assert_eq!(vec2.capacity(), 16);
/// ```
pub type SliceVec<'a, T, I = usize> = Vec<T, crate::storage::SliceStorage<'a, T>, I>;
/// A vector using an arena-allocated slice for storage.
///
/// See [`Arena::try_vec`](crate::Arena::try_vec) for example usage.
pub type ArenaVec<'a, T, I = usize> = Vec<T, crate::storage::ArenaStorage<'a, ArrayLike<T>>, I>;

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> From<S> for Vec<T, S, I> {
    /// Converts a contiguous block of memory into an empty vector.
    ///
    /// # Panics
    /// This may panic if the index type I cannot represent `buf.capacity()`.
    fn from(buf: S) -> Self {
        if buf.capacity() > I::MAX_REPRESENTABLE {
            buffer_too_large_for_index_type::<I>();
        }

        Vec {
            len: I::from_usize(0),
            buf,
            elem: PhantomData,
        }
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> Vec<T, S, I> {
    /// Decomposes a `Vec<T, S, I>` into its raw parts.
    ///
    /// Returns the raw storage type and the length of the vector in elements.
    /// These are the same arguments in the same order as the arguments to
    /// [`from_raw_parts`](Vec::from_raw_parts).
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 5];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.extend(&[1, 2, 3]);
    ///
    /// let (slice, len) = vec.into_raw_parts();
    /// unsafe {
    ///     assert_eq!(slice[0].assume_init(), 1);
    ///     assert_eq!(slice[1].assume_init(), 2);
    ///     assert_eq!(slice[2].assume_init(), 3);
    ///     // other elements are uninitialized
    /// }
    /// ```
    pub fn into_raw_parts(self) -> (S, I) {
        let ptr = (&self.buf) as *const S;
        let result = (unsafe { ptr.read() }, self.len);
        core::mem::forget(self);
        result
    }

    /// Creates a `Vec<T, S, I>` directly from its raw parts.
    ///
    /// # Safety
    /// Callers must ensure that values stored in `buf` at all positions less
    /// than `length` are initialized, and that `length` is less than or equal
    /// to `buf.capacity()`.
    ///
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 5];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.extend(&[1, 2, 3]);
    ///
    /// let (buf, length) = vec.into_raw_parts();
    /// let vec = unsafe { coca::SliceVec::<u32>::from_raw_parts(buf, length) };
    /// assert_eq!(vec.as_slice(), &[1, 2, 3]);
    /// ```
    pub unsafe fn from_raw_parts(buf: S, length: I) -> Self {
        Vec {
            buf,
            len: length,
            elem: PhantomData,
        }
    }

    /// Returns the number of elements the vector can hold.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Returns the number of elements in the vector, also referred to as its *length*.
    #[inline]
    pub fn len(&self) -> usize {
        self.len.as_usize()
    }

    #[inline]
    fn set_len(&mut self, new_len: I) {
        debug_assert!(new_len.as_usize() <= self.capacity());
        self.len = new_len;
    }

    /// Returns `true` if the vector contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len.as_usize() == 0
    }

    /// Returns `true` if the vector contains the maximum number of elements.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len.as_usize() == self.buf.capacity()
    }

    /// Removes the last element from the vector and returns it, or [`None`] if it is empty.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 3];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.push(1); vec.push(2); vec.push(3);
    /// assert_eq!(vec.pop(), Some(3));
    /// assert_eq!(vec, &[1, 2][..]);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        self.len = I::from_usize(self.len() - 1);
        unsafe { Some(ptr_at_index(&self.buf, self.len()).read()) }
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// Equivalent to `&s[..]`.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self
    }

    /// Extracts a mutable slice of the entire vector.
    ///
    /// Equivalent to `&mut s[..]`.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self
    }

    /// Returns a reference to the element at the specified index, or [`None`]
    /// if the index is out of bounds.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 3];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.push(1); vec.push(2); vec.push(3);
    /// assert_eq!(vec.get(1), Some(&2));
    /// assert_eq!(vec.get(3), None);
    /// ```
    #[inline]
    pub fn get(&self, index: I) -> Option<&T> {
        let index = index.as_usize();
        if self.len() <= index {
            return None;
        }

        unsafe { Some(ptr_at_index(&self.buf, index).as_ref().unwrap()) }
    }

    /// Returns a mutable reference to the element at the specified index, or
    /// [`None`] if the index is out of bounds.
    #[inline]
    pub fn get_mut(&mut self, index: I) -> Option<&mut T> {
        let index = index.as_usize();
        if self.len() <= index {
            return None;
        }

        unsafe { Some(mut_ptr_at_index(&mut self.buf, index).as_mut().unwrap()) }
    }

    /// Appends an element to the back of the vector, returning `Err(value)` if
    /// it is already at capacity.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 3];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// assert!(vec.try_push(1).is_ok());
    /// assert!(vec.try_push(2).is_ok());
    /// assert!(vec.try_push(3).is_ok());
    /// assert_eq!(vec.try_push(4), Err(4));
    /// ```
    #[inline]
    pub fn try_push(&mut self, value: T) -> Result<(), T> {
        if self.is_full() {
            return Err(value);
        }

        let len = self.len();
        unsafe { mut_ptr_at_index(&mut self.buf, len).write(value) };

        self.len = I::from_usize(len + 1);
        Ok(())
    }

    /// Appends an element to the back of the vector.
    ///
    /// # Panics
    /// Panics if the vector is already at capacity. See [`try_push`](Vec::try_push)
    /// for a checked version that never panics.
    #[inline]
    pub fn push(&mut self, value: T) {
        #[cold]
        #[inline(never)]
        fn assert_failed() -> ! {
            panic!("vector is already at capacity")
        }

        if self.try_push(value).is_err() {
            assert_failed();
        }
    }

    /// Shortens the vector, keeping the first `len` elements and dropping the rest.
    ///
    /// If `len` is greater than the vector's current length, this has no effect.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 4];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.push(1); vec.push(2); vec.push(3); vec.push(4);
    ///
    /// vec.truncate(6);
    /// assert_eq!(vec, &[1, 2, 3, 4][..]);
    ///
    /// vec.truncate(2);
    /// assert_eq!(vec, &[1, 2][..]);
    /// ```
    pub fn truncate(&mut self, len: I) {
        let new_len = len.as_usize();
        let old_len = self.len.as_usize();

        if new_len >= old_len {
            return;
        }

        for i in new_len..old_len {
            unsafe { mut_ptr_at_index(&mut self.buf, i).drop_in_place() };
        }

        self.len = len;
    }

    /// Clears the vector, dropping all values.
    ///
    /// Equivalent to `s.truncate(0)`.
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(I::from_usize(0))
    }

    /// Swaps two elements in the vector.
    ///
    /// # Panics
    /// Panics if either argument is out of bounds.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 4];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.push(1); vec.push(2); vec.push(3); vec.push(4);
    ///
    /// vec.swap(0, 2);
    /// assert_eq!(vec, &[3, 2, 1, 4][..]);
    /// ```
    #[inline]
    pub fn swap(&mut self, fst: I, snd: I) {
        let fst = fst.as_usize();
        let snd = snd.as_usize();
        self.as_mut_slice().swap(fst, snd);
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector. This
    /// does not preserve ordering, but it is O(1).
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 4];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.push(1); vec.push(2); vec.push(3); vec.push(4);
    ///
    /// vec.swap_remove(1);
    /// assert_eq!(vec, &[1, 4, 3][..]);
    /// ```
    #[inline]
    pub fn swap_remove(&mut self, index: I) -> T {
        #[cold]
        #[inline(never)]
        fn assert_failed(idx: usize, len: usize) -> ! {
            panic!(
                "swap_remove index (is {}) should be < len (is {})",
                idx, len
            );
        }

        let idx = index.as_usize();
        let len = self.len.as_usize();
        if idx >= len {
            assert_failed(idx, len);
        }

        unsafe {
            let last = ptr_at_index(&self.buf, len - 1).read();
            let hole = mut_ptr_at_index(&mut self.buf, idx);
            self.len = I::from_usize(self.len() - 1);
            ptr::replace(hole, last)
        }
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// # Panics
    /// Panics if the vector is already full, or if `index` is out of bounds.
    /// See [`try_insert`](Vec::try_insert) for a checked version.
    pub fn insert(&mut self, index: I, element: T) {
        #[cold]
        #[inline(never)]
        fn assert_failed() -> ! {
            panic!("vector is already at capacity")
        }

        let result = self.try_insert(index, element);
        if result.is_err() {
            assert_failed();
        }
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// Returns back `Err(element)` if the vector is already at capacity.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 4];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.push(1); vec.push(2); vec.push(3);
    ///
    /// assert!(vec.try_insert(3, 4).is_ok());
    /// assert!(vec.try_insert(4, 5).is_err());
    /// assert_eq!(vec, &[1, 2, 3, 4][..]);
    /// ```
    pub fn try_insert(&mut self, index: I, element: T) -> Result<(), T> {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!(
                "insertion index (is {}) should be <= len (is {})",
                index, len
            );
        }

        if self.is_full() {
            return Err(element);
        }

        let idx = index.as_usize();
        let len = self.len.as_usize();
        if idx > len {
            assert_failed(idx, len);
        }

        let p = mut_ptr_at_index(&mut self.buf, idx);
        unsafe {
            ptr::copy(p, p.add(1), len - idx);
            ptr::write(p, element);
        }

        self.len = I::from_usize(len + 1);
        Ok(())
    }

    /// Places an element at position `index` within the vector, returning the
    /// element previously stored there.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 4];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.push(1); vec.push(2); vec.push(3);
    ///
    /// assert_eq!(vec.replace(1, 4), 2);
    /// assert_eq!(vec, &[1, 4, 3][..]);
    /// ```
    pub fn replace(&mut self, index: I, element: T) -> T {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!(
                "replacement index (is {}) should be < len (is {})",
                index, len
            );
        }

        let idx = index.as_usize();
        let len = self.len.as_usize();
        if idx >= len {
            assert_failed(idx, len);
        }

        let p = mut_ptr_at_index(&mut self.buf, idx);
        unsafe { ptr::replace(p, element) }
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 4];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.push(1); vec.push(2); vec.push(3);
    /// vec.remove(0);
    ///
    /// assert_eq!(vec, &[2, 3][..]);
    /// ```
    pub fn remove(&mut self, index: I) -> T {
        #[cold]
        #[inline(never)]
        fn assert_failed(idx: usize, len: usize) -> ! {
            panic!("removal index (is {}) should be < len (is {})", idx, len);
        }

        let idx = index.as_usize();
        let len = self.len.as_usize();
        if idx >= len {
            assert_failed(idx, len);
        }

        unsafe {
            let ret;
            {
                let p = mut_ptr_at_index(&mut self.buf, idx);
                ret = ptr::read(p);
                ptr::copy(p.offset(1), p, len - idx - 1);
            }

            self.len = I::from_usize(len - 1);
            ret
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns false.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 4];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.push(1); vec.push(2); vec.push(3); vec.push(4);
    /// vec.retain(|&x| x % 2 == 0);
    ///
    /// assert_eq!(vec, &[2, 4][..]);
    /// ```
    /// The exact order may be useful for tracking external state, like an index.
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 4];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.push(1); vec.push(2); vec.push(3); vec.push(4);
    /// let keep = [false, true, true, false];
    /// let mut i = 0;
    /// vec.retain(|_| (keep[i], i += 1).0);
    ///
    /// assert_eq!(vec, &[2, 3][..]);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.drain_filter(|_, item| !f(&*item));
    }

    /// Creates a draining iterator that removes the specified range in the vector
    /// and yields the removed items.
    ///
    /// When the iterator **is** dropped, all elements in the range are removed
    /// from the vector, even if the iterator was not fully consumed. If the
    /// iterator **is not** dropped (with [`core::mem::forget`] for example),
    /// it is unspecified how many elements are removed.
    ///
    /// # Panics
    /// Panics if the starting point is greater than the end point or if the end
    /// point is greater than the length of the vector.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 5];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.push(1); vec.push(2); vec.push(3); vec.push(4); vec.push(5);
    /// let mut iter = vec.drain(1..3);
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(3));
    /// assert_eq!(iter.next(), None);
    /// drop(iter);
    /// assert_eq!(vec, &[1, 4, 5][..]);
    /// ```
    pub fn drain<R: RangeBounds<I>>(&mut self, range: R) -> Drain<'_, T, S, I> {
        let Range { start, end } = normalize_range(range, self.len());

        // prevent leaking a Drain iterator from leaving the vector
        // in an invalid state potentially causing undefined behaviour
        let original_len = self.len();
        self.len = I::from_usize(start);

        Drain {
            parent: self,
            original_len,
            target_start: start,
            front_index: start,
            back_index: end,
            target_end: end,
        }
    }

    /// Creates an iterator which uses a closure to determine if an element
    /// should be removed.
    /// 
    /// If the closure returns `true`, the element is removed and yielded.
    /// If the closure returns `false`, the element will remain in the vector
    /// and will not be yielded by the iterator.
    /// 
    /// When the iterator **is** dropped, all remaining items matching the
    /// filter are removed from the vector, even if the iterator was not fully
    /// consumed. If the iterator **is not** dropped (with [`core::mem::forget`]
    /// for example), it is unspecified how many elements are removed.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 5];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.push(1); vec.push(2); vec.push(3); vec.push(4); vec.push(5);
    /// {
    ///     let mut it = vec.drain_filter(
    ///         |_idx, num| if *num % 2 == 0 { true } else { *num *= 2; false }
    ///     );
    ///     assert_eq!(it.next(), Some(2));
    ///     assert_eq!(it.next(), Some(4));
    ///     assert_eq!(it.next(), None);
    /// }
    /// assert_eq!(vec, [2, 6, 10]);
    /// ```
    pub fn drain_filter<F: FnMut(I, &mut T) -> bool>(&mut self, filter: F) -> DrainFilter<'_, T, S, I, F> {
        self.drain_filter_range(.., filter)
    }

    /// Creates an iterator which uses a closure to determine if an element
    /// in the specified range should be removed.
    /// 
    /// If the closure returns `true`, the element is removed and yielded.
    /// If the closure returns `false`, the element will remain in the vector
    /// and will not be yielded by the iterator.
    /// 
    /// When the iterator **is** dropped, all remaining items matching the
    /// filter are removed from the vector, even if the iterator was not fully
    /// consumed. If the iterator **is not** dropped (with [`core::mem::forget`]
    /// for example), it is unspecified how many elements are removed.
    ///
    /// # Panics
    /// Panics if the starting point is greater than the end point or if the end
    /// point is greater than the length of the vector.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 5];
    /// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.push(1); vec.push(2); vec.push(3); vec.push(4); vec.push(5);
    /// {
    ///     let mut it = vec.drain_filter_range(1..=3,
    ///         |_idx, num| if *num % 2 == 0 { true } else { *num *= 2; false }
    ///     );
    ///     assert_eq!(it.next(), Some(2));
    ///     assert_eq!(it.next(), Some(4));
    ///     assert_eq!(it.next(), None);
    /// }
    /// assert_eq!(vec, [1, 6, 5]);
    /// ```
    pub fn drain_filter_range<R: RangeBounds<I>, F: FnMut(I, &mut T) -> bool>(&mut self, range: R, filter: F) -> DrainFilter<'_, T, S, I, F> {
        let Range { start, end } = normalize_range(range, self.len());

        // prevent leaking a DrainFilter from leaving the vector in
        // an invalid state potentially causing undefined behaviour
        let original_len = self.len();
        self.len = I::from_usize(start);

        DrainFilter {
            parent: self,
            filter_fn: filter,
            original_len,
            target_start: start,
            front_index: start,
            back_index: end,
            target_end: end,
        }
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> core::ops::Deref for Vec<T, S, I> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        unsafe {
            let ptr = self.buf.get_ptr() as *const T;
            core::slice::from_raw_parts(ptr, self.len.as_usize())
        }
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> core::ops::DerefMut for Vec<T, S, I> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe {
            let ptr = self.buf.get_mut_ptr() as *mut T;
            core::slice::from_raw_parts_mut(ptr, self.len.as_usize())
        }
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> core::ops::Index<I> for Vec<T, S, I> {
    type Output = T;
    fn index(&self, index: I) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> core::ops::IndexMut<I> for Vec<T, S, I> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.get_mut(index).unwrap()
    }
}

macro_rules! _impl_idx_range {
    ($self:ident, $idx:ident: $r:ty, $lo:expr, $hi:expr) => {
        impl<T, S: Storage<ArrayLike<T>>, I: Capacity> core::ops::Index<$r> for Vec<T, S, I> {
            type Output = [T];
            #[allow(unused_variables)]
            fn index(&self, $idx: $r) -> &Self::Output {
                let $self = self;
                let start = $lo;
                let end = $hi;
                &self.as_slice()[start..end]
            }
        }

        impl<T, S: Storage<ArrayLike<T>>, I: Capacity + PartialOrd> core::ops::IndexMut<$r>
            for Vec<T, S, I>
        {
            #[allow(unused_variables)]
            fn index_mut(&mut self, $idx: $r) -> &mut Self::Output {
                let (start, end) = {
                    let $self = &self;
                    ($lo, $hi)
                };
                &mut self.as_mut_slice()[start..end]
            }
        }
    };
}

_impl_idx_range! { s, index: core::ops::Range<I>, index.start.as_usize(), index.end.as_usize() }
_impl_idx_range! { s, index: core::ops::RangeFrom<I>, index.start.as_usize(), s.len() }
_impl_idx_range! { s, index: core::ops::RangeFull, 0, s.len() }
_impl_idx_range! { s, index: core::ops::RangeInclusive<I>, index.start().as_usize(), index.end().as_usize().saturating_add(1) }
_impl_idx_range! { s, index: core::ops::RangeTo<I>, 0, index.end.as_usize() }
_impl_idx_range! { s, index: core::ops::RangeToInclusive<I>, 0, index.end.as_usize().saturating_add(1) }

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> core::convert::AsRef<[T]> for Vec<T, S, I> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> core::convert::AsMut<[T]> for Vec<T, S, I> {
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> core::ops::Drop for Vec<T, S, I> {
    fn drop(&mut self) {
        unsafe {
            let ptr = self.buf.get_mut_ptr() as *mut T;
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(ptr, self.len()))
        }
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> core::fmt::Debug for Vec<T, S, I>
where
    T: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> Hash for Vec<T, S, I>
where
    T: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

impl<AT, AS, AI, BT, BS, BI> PartialEq<Vec<BT, BS, BI>> for Vec<AT, AS, AI>
where
    AT: PartialEq<BT>,
    AS: Storage<ArrayLike<AT>>,
    BS: Storage<ArrayLike<BT>>,
    AI: Capacity,
    BI: Capacity,
{
    #[inline]
    fn eq(&self, other: &Vec<BT, BS, BI>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T: Eq, S: Storage<ArrayLike<T>>, I: Capacity> Eq for Vec<T, S, I> {}

impl<V, T: PartialEq<V>, S: Storage<ArrayLike<T>>, I: Capacity> PartialEq<&[V]> for Vec<T, S, I> {
    #[inline]
    fn eq(&self, other: &&[V]) -> bool {
        self.as_slice() == &other[..]
    }
}

impl<V, T, S: Storage<ArrayLike<T>>, I: Capacity> PartialEq<&mut [V]> for Vec<T, S, I>
where
    T: PartialEq<V>,
{
    #[inline]
    fn eq(&self, other: &&mut [V]) -> bool {
        self.as_slice() == &other[..]
    }
}

impl<V: PartialEq<T>, T, S: Storage<ArrayLike<T>>, I: Capacity> PartialEq<Vec<T, S, I>> for &[V] {
    #[inline]
    fn eq(&self, other: &Vec<T, S, I>) -> bool {
        &self[..] == other.as_slice()
    }
}

impl<V, T, S: Storage<ArrayLike<T>>, I: Capacity> PartialEq<Vec<T, S, I>> for &mut [V]
where
    V: PartialEq<T>,
{
    #[inline]
    fn eq(&self, other: &Vec<T, S, I>) -> bool {
        &self[..] == other.as_slice()
    }
}

impl<T: PartialOrd, S: Storage<ArrayLike<T>>, I: Capacity> PartialOrd for Vec<T, S, I> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}

impl<T: Ord, S: Storage<ArrayLike<T>>, I: Capacity> Ord for Vec<T, S, I> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_slice().cmp(&other.as_slice())
    }
}

impl<T, S: Storage<ArrayLike<T>>, Idx: Capacity> core::iter::Extend<T> for Vec<T, S, Idx> {
    fn extend<I: core::iter::IntoIterator<Item = T>>(&mut self, iter: I) {
        for element in iter {
            self.push(element);
        }
    }
}

impl<'a, T, S: Storage<ArrayLike<T>>, Idx: Capacity> core::iter::Extend<&'a T> for Vec<T, S, Idx>
where
    T: 'a + Clone,
{
    fn extend<I: core::iter::IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        for element in iter {
            self.push(element.clone());
        }
    }
}

/// An iterator that moves out of a vector.
///
/// This `struct` is created by the `into_iter` method on [`Vec`] (provided by
/// the [`IntoIterator`] trait).
///
/// # Example
/// ```
/// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 4];
/// let mut vec = coca::SliceVec::<u32>::from(&mut backing_region[..]);
/// # vec.push(1); vec.push(2);
/// let mut iter: coca::vec::IntoIterator<_, _, _> = vec.into_iter();
/// # assert_eq!(iter.next(), Some(1));
/// # assert_eq!(iter.next(), Some(2));
/// # assert_eq!(iter.next(), None);
/// ```
pub struct IntoIterator<T, S: Storage<ArrayLike<T>>, I: Capacity> {
    start: I,
    end: I,
    buf: S,
    elems: PhantomData<T>,
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> Iterator for IntoIterator<T, S, I> {
    type Item = T;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.end.as_usize() - self.start.as_usize();
        (size, Some(size))
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let start = self.start.as_usize();
        let end = self.end.as_usize();
        if start >= end {
            return None;
        }

        let ptr = (self.buf.get_ptr() as *const T).wrapping_add(start);
        let ret = unsafe { ptr.read() };
        self.start = I::from_usize(start + 1);

        Some(ret)
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> DoubleEndedIterator for IntoIterator<T, S, I> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let start = self.start.as_usize();
        let end = self.end.as_usize();
        if start >= end {
            return None;
        }

        let end = end - 1;
        let ptr = (self.buf.get_ptr() as *const T).wrapping_add(end);
        let ret = unsafe { ptr.read() };
        self.end = I::from_usize(end);

        Some(ret)
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> ExactSizeIterator for IntoIterator<T, S, I> {}
impl<T, S: Storage<ArrayLike<T>>, I: Capacity> FusedIterator for IntoIterator<T, S, I> {}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> Drop for IntoIterator<T, S, I> {
    fn drop(&mut self) {
        self.for_each(drop);
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> IntoIter for Vec<T, S, I> {
    type Item = T;
    type IntoIter = IntoIterator<T, S, I>;

    fn into_iter(self) -> Self::IntoIter {
        let end = self.len;
        let buf = unsafe { (&self.buf as *const S).read() };
        core::mem::forget(self);

        IntoIterator {
            start: I::from_usize(0),
            end,
            buf,
            elems: PhantomData,
        }
    }
}

impl<'a, T, S: Storage<ArrayLike<T>>, I: Capacity> IntoIter for &'a Vec<T, S, I> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

impl<'a, T, S: Storage<ArrayLike<T>>, I: Capacity> IntoIter for &'a mut Vec<T, S, I> {
    type Item = &'a mut T;
    type IntoIter = core::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_mut_slice().iter_mut()
    }
}

/// A draining iterator for `Vec<T>`.
///
/// This `struct` is created by [`Vec::drain`]. See its documentation for more.
pub struct Drain<'p, T, S: Storage<ArrayLike<T>>, I: Capacity> {
    parent: &'p mut Vec<T, S, I>,
    original_len: usize,
    target_start: usize,
    front_index: usize,
    back_index: usize,
    target_end: usize,
}

impl<'p, T, S: Storage<ArrayLike<T>>, I: Capacity> Iterator for Drain<'p, T, S, I> {
    type Item = T;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.back_index - self.front_index;
        (size, Some(size))
    }

    fn next(&mut self) -> Option<Self::Item> {
        if self.front_index == self.back_index {
            return None;
        }

        let out = unsafe { self.parent.as_slice().as_ptr().add(self.front_index).read() };
        self.front_index += 1;
        Some(out)
    }
}

impl<'p, T, S: Storage<ArrayLike<T>>, I: Capacity> DoubleEndedIterator for Drain<'p, T, S, I> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.front_index == self.back_index {
            return None;
        }

        self.back_index -= 1;
        unsafe { Some(self.parent.as_slice().as_ptr().add(self.back_index).read()) }
    }
}

impl<'p, T, S: Storage<ArrayLike<T>>, I: Capacity> ExactSizeIterator for Drain<'p, T, S, I> {}
impl<'p, T, S: Storage<ArrayLike<T>>, I: Capacity> FusedIterator for Drain<'p, T, S, I> {}

impl<'p, T, S: Storage<ArrayLike<T>>, I: Capacity> Drop for Drain<'p, T, S, I> {
    fn drop(&mut self) {
        self.for_each(drop);

        let count = self.original_len - self.target_end;
        let src = unsafe { self.parent.as_slice().as_ptr().add(self.target_end) };
        let dst = unsafe { self.parent.as_mut_slice().as_mut_ptr().add(self.target_start) };
        unsafe { ptr::copy(src, dst, count) };

        let removed = self.target_end - self.target_start;
        let new_len = I::from_usize(self.original_len - removed);
        self.parent.set_len(new_len);
    }
}

/// An iterator which uses a closure to determine if an element should be removed.
/// 
/// This struct is created by [`Vec::drain_filter`]. See its documentation for more.
pub struct DrainFilter<'p, T, S: Storage<ArrayLike<T>>, I: Capacity, F: FnMut(I, &mut T) -> bool> {
    parent: &'p mut Vec<T, S, I>,
    filter_fn: F,
    original_len: usize,
    target_start: usize,
    front_index: usize,
    back_index: usize,
    target_end: usize,
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity, F: FnMut(I, &mut T) -> bool> Iterator for DrainFilter<'_, T, S, I, F> {
    type Item = T;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let max_len = self.back_index - self.front_index;
        (0, Some(max_len))
    }

    fn next(&mut self) -> Option<Self::Item> {
        while self.front_index != self.back_index {
            let src = unsafe { self.parent.as_mut_slice().as_mut_ptr().add(self.front_index) };
            let item = unsafe { src.as_mut().unwrap() };
            self.front_index += 1;
            if (self.filter_fn)(I::from_usize(self.front_index), item) {
                return Some(unsafe { src.read() });
            } else {
                let dst = unsafe { self.parent.as_mut_slice().as_mut_ptr().add(self.target_start) };
                unsafe { ptr::copy(src as *const T, dst, 1) };
                self.target_start += 1;
            }
        }

        None
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity, F: FnMut(I, &mut T) -> bool> DoubleEndedIterator for DrainFilter<'_, T, S, I, F> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while self.front_index != self.back_index {
            self.back_index -= 1;
            let src = unsafe { self.parent.as_mut_slice().as_mut_ptr().add(self.back_index) };
            let item = unsafe { src.as_mut().unwrap() };
            if (self.filter_fn)(I::from_usize(self.back_index), item) {
                return Some(unsafe { src.read() });
            } else {
                self.target_end -= 1;
                let dst = unsafe { self.parent.as_mut_slice().as_mut_ptr().add(self.target_end) };
                unsafe { ptr::copy(src as *const T, dst, 1) };
            }
        }

        None
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity, F: FnMut(I, &mut T) -> bool> FusedIterator for DrainFilter<'_, T, S, I, F> {}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity, F: FnMut(I, &mut T) -> bool> Drop for DrainFilter<'_, T, S, I, F> {
    fn drop(&mut self) {
        self.for_each(drop);
        
        let count = self.original_len - self.target_end;
        let src = unsafe { self.parent.as_slice().as_ptr().add(self.target_end) };
        let dst = unsafe { self.parent.as_mut_slice().as_mut_ptr().add(self.target_start) };
        unsafe { ptr::copy(src, dst, count) };

        let removed = self.target_end - self.target_start;
        let new_len = I::from_usize(self.original_len - removed);
        self.parent.len = new_len;
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
/// A vector using a heap-allocated slice for storage.
///
/// Note this still has a fixed capacity, and will never reallocate.
///
/// # Examples
/// ```
/// let mut vec = coca::AllocVec::<char>::with_capacity(3);
/// vec.push('a');
/// vec.push('b');
/// vec.push('c');
/// assert!(vec.try_push('d').is_err());
/// ```
pub type AllocVec<T, I = usize> = Vec<T, crate::storage::AllocStorage<ArrayLike<T>>, I>;

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<T: Copy, I: Capacity> AllocVec<T, I> {
    /// Constructs a new, empty `AllocVec<T, I>` with the specified capacity.
    ///
    /// # Panics
    /// Panics if the specified capacity cannot be represented by a `usize`.
    pub fn with_capacity(capacity: I) -> Self {
        let cap = capacity.as_usize();
        if capacity != I::from_usize(cap) {
            buffer_too_large_for_index_type::<I>();
        }

        Vec {
            len: I::from_usize(0),
            buf: crate::storage::AllocStorage::with_capacity(cap),
            elem: PhantomData,
        }
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<T: Copy, I: Capacity> Clone for AllocVec<T, I> {
    fn clone(&self) -> Self {
        let mut result = Self::with_capacity(I::from_usize(self.capacity()));
        for item in self.iter() {
            result.push(*item);
        }
        result
    }
}

/// A vector using an inline array for storage.
///
/// # Examples
/// ```
/// let mut vec = coca::InlineVec::<char, 3>::new();
/// vec.push('a');
/// vec.push('b');
/// vec.push('c');
/// assert!(vec.try_push('d').is_err());
/// ```
pub type InlineVec<T, const C: usize> = Vec<T, InlineStorage<T, C>, usize>;

/// A vector using an inline array for storage, generic over the index type.
///
/// # Examples
/// ```
/// let mut vec = coca::TiInlineVec::<char, u8, 3>::new();
/// vec.push('a');
/// assert_eq!(vec[0u8], 'a');
/// ```
pub type TiInlineVec<T, Index, const C: usize> = Vec<T, InlineStorage<T, C>, Index>;

impl<T, I: Capacity, const C: usize> Vec<T, InlineStorage<T, C>, I> {
    /// Constructs a new, empty `Vec` backed by an inline array.
    ///
    /// # Panics
    /// Panics if `C` cannot be represented as a value of type `I`.
    ///
    /// # Examples
    /// ```
    /// let vec = coca::InlineVec::<u32, 6>::new();
    /// assert_eq!(vec.capacity(), 6);
    /// assert_eq!(vec.len(), 0);
    /// ```
    #[inline]
    pub fn new() -> Self {
        if C > I::MAX_REPRESENTABLE {
            buffer_too_large_for_index_type::<I>();
        }

        Vec {
            len: I::from_usize(0),
            buf: unsafe { MaybeUninit::uninit().assume_init() },
            elem: PhantomData,
        }
    }
}

impl<T, I: Capacity, const C: usize> Default for Vec<T, InlineStorage<T, C>, I> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone, I: Capacity, const C: usize> core::clone::Clone for Vec<T, InlineStorage<T, C>, I> {
    fn clone(&self) -> Self {
        let mut ret = Self::new();
        ret.clone_from(self);
        ret
    }

    fn clone_from(&mut self, source: &Self) {
        self.clear();
        for next in source {
            self.push(next.clone());
        }
    }
}

impl<T: Clone, I: Capacity, const C: usize> From<&[T]> for Vec<T, InlineStorage<T, C>, I> {
    fn from(source: &[T]) -> Self {
        if C > I::MAX_REPRESENTABLE {
            buffer_too_large_for_index_type::<I>();
        }

        if source.len() > C {
            panic!(
                "source should not have more than {} elements (has {})",
                C,
                source.len()
            );
        }

        let mut ret = Self::new();
        for next in source {
            ret.push(next.clone());
        }
        ret
    }
}

impl<T: Clone, I: Capacity, const C: usize> From<&mut [T]> for Vec<T, InlineStorage<T, C>, I> {
    fn from(source: &mut [T]) -> Self {
        if C > I::MAX_REPRESENTABLE {
            buffer_too_large_for_index_type::<I>();
        }

        if source.len() > C {
            panic!(
                "source should not have more than {} elements (has {})",
                C,
                source.len()
            );
        }

        let mut ret = Self::new();
        for next in source {
            ret.push(next.clone());
        }
        ret
    }
}

impl<V: PartialEq<T>, T, S, I, const N: usize> PartialEq<Vec<T, S, I>> for [V; N]
where
    V: PartialEq<T>,
    S: Storage<ArrayLike<T>>,
    I: Capacity,
{
    #[inline]
    fn eq(&self, other: &Vec<T, S, I>) -> bool {
        &self[..] == other.as_slice()
    }
}

impl<V, T, S, I, const N: usize> PartialEq<[V; N]> for Vec<T, S, I>
where
    T: PartialEq<V>,
    S: Storage<ArrayLike<T>>,
    I: Capacity,
{
    #[inline]
    fn eq(&self, other: &[V; N]) -> bool {
        self.as_slice() == &other[..]
    }
}

impl<T, I: Capacity, const C: usize> core::iter::FromIterator<T>
    for Vec<T, InlineStorage<T, C>, I>
{
    /// Creates a vector backed by an inline array from an iterator.
    ///
    /// # Panics
    /// Panics if the iterator yields more than `N` elements.
    fn from_iter<It: core::iter::IntoIterator<Item = T>>(iter: It) -> Self {
        let mut result = Self::new();
        result.extend(iter);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn from_panics_for_too_large_inputs() {
        let mut backing_array = [core::mem::MaybeUninit::<char>::uninit(); 300];
        let _ = SliceVec::<char, u8>::from(&mut backing_array[..]);
    }

    #[test]
    fn sizes_of_instantiated_types() {
        use core::mem::size_of;

        assert_eq!(size_of::<SliceVec<u64, usize>>(), 3 * size_of::<usize>());
        assert_eq!(size_of::<ArenaVec<u64, usize>>(), 3 * size_of::<usize>());

        #[cfg(feature = "alloc")]
        assert_eq!(size_of::<AllocVec<u64, usize>>(), 3 * size_of::<usize>());

        assert_eq!(size_of::<InlineVec<u8, 8>>(), size_of::<usize>() + 8);
        assert_eq!(size_of::<TiInlineVec<u8, u8, 99>>(), 100);
        assert_eq!(
            size_of::<Vec<u32, &mut [MaybeUninit<u32>; 1000], usize>>(),
            2 * size_of::<usize>()
        );
    }

    #[test]
    fn iterators_take_and_drop_correctly() {
        use core::cell::Cell;

        #[derive(Clone)]
        struct Droppable<'a> {
            value: usize,
            counter: &'a Cell<usize>,
        }

        impl Drop for Droppable<'_> {
            fn drop(&mut self) {
                let count = self.counter.get();
                self.counter.set(count + 1);
            }
        }

        let drop_count = Cell::new(0usize);

        let mut backing_region = [
            core::mem::MaybeUninit::<Droppable>::uninit(),
            core::mem::MaybeUninit::<Droppable>::uninit(),
            core::mem::MaybeUninit::<Droppable>::uninit(),
            core::mem::MaybeUninit::<Droppable>::uninit(),
            core::mem::MaybeUninit::<Droppable>::uninit(),
            core::mem::MaybeUninit::<Droppable>::uninit(),
            core::mem::MaybeUninit::<Droppable>::uninit(),
            core::mem::MaybeUninit::<Droppable>::uninit(),
        ];

        let mut vec = SliceVec::<Droppable>::from(&mut backing_region[..]);
        for i in 1..=8 {
            vec.push(Droppable {
                value: i,
                counter: &drop_count,
            });
        }

        let mut drain_iter = vec.drain(2..=5);
        assert_eq!(drain_iter.next_back().unwrap().value, 6);
        assert_eq!(drop_count.get(), 1);

        drop(drain_iter);
        assert_eq!(drop_count.get(), 4);

        let mut into_iter = vec.into_iter();
        assert_eq!(into_iter.next().unwrap().value, 1);
        assert_eq!(into_iter.next().unwrap().value, 2);
        assert_eq!(into_iter.next().unwrap().value, 7);
        assert_eq!(drop_count.get(), 7);

        drop(into_iter);
        assert_eq!(drop_count.get(), 8);

        let mut vec = SliceVec::<Droppable>::from(&mut backing_region[..]);
        for i in 1..=8 {
            vec.push(Droppable {
                value: i,
                counter: &drop_count,
            });
        }
        drop(vec);
        assert_eq!(drop_count.get(), 16);
    }

    #[test]
    #[should_panic]
    fn leaking_drain() {
        let mut a = 1;
        let mut b = 2;
        let mut c = 3;

        let mut backing_region = [
            core::mem::MaybeUninit::<&mut i32>::uninit(),
            core::mem::MaybeUninit::<&mut i32>::uninit(),
            core::mem::MaybeUninit::<&mut i32>::uninit(),
            core::mem::MaybeUninit::<&mut i32>::uninit(),
        ];
        let mut vec = SliceVec::<&mut i32>::from(&mut backing_region[..]);
        vec.push(&mut a);
        vec.push(&mut b);
        vec.push(&mut c);

        let mut it = vec.drain(1..);
        if let Some(cloned_ref) = it.next_back() {
            core::mem::forget(it);

            if let Some(original_ref) = vec.pop() {
                let clone = cloned_ref as *mut i32 as usize;
                let original = original_ref as *mut i32 as usize;

                assert_eq!(clone, original);
            }
        }
    }
}
