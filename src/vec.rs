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
//! [references to slices](SliceVec) and [arena-allocated slices](ArenaVec).
//!
//! The `nightly` feature allows using [arrays inlined in the `Vec`](ArrayVec)
//! for storage, as well as referenced and (arena-)boxed arrays, which do not
//! require a runtime representation of their capacity.
//!
//! The `alloc` feature allows using [owned slices](HeapVec) for storage. Note
//! that such a vector still does not reallocate - this may be useful in cases
//! where domain logic dictates a length limit on a list.
//!
//! Specifying an index type smaller than `usize`, such as `u16` or even `u8`,
//! can aid in struct size optimization, especially with `ArrayVec`. It's also
//! possible to [declare new types](index_type!) for this purpose, leveraging
//! the type system to avoid using the wrong kind of index.
//!
//! Because the capacity is constant, operations that grow the vector,
//! such as [`push`](Vec::push) and [`insert`](Vec::insert), may fail.
//! Checked versions of these methods are provided ([`try_push`](Vec::try_push),
//! [`try_insert`](Vec::try_insert)).

use crate::storage::{Capacity, ContiguousStorage};

use core::hash::{Hash, Hasher};
use core::iter::{IntoIterator as IntoIter, Iterator};
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ops::RangeBounds;
use core::ptr;

/// A contiguous growable array type with constant capacity.
///
/// Generic over the storage buffer type `Buf` and the index type `Idx`.
///
/// See the [module-level documentation](crate::vec) for more.
pub struct Vec<Element, Buf, Idx = usize>
where
    Buf: ContiguousStorage<Element>,
    Idx: Capacity,
{
    len: Idx,
    buf: Buf,
    elem: PhantomData<Element>,
}

/// A vector using any mutable slice for storage.
pub type SliceVec<'a, E, I = usize> = Vec<E, crate::storage::SliceStorage<'a, E>, I>;
/// A vector using an arena-allocated slice for storage.
pub type ArenaVec<'a, E, I = usize> = Vec<E, crate::storage::ArenaStorage<'a, E>, I>;

impl<E, B, I> From<B> for Vec<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn from(buf: B) -> Self {
        I::from_usize(buf.storage().len()); // panics if I cannot index the whole array

        Vec {
            len: I::from_usize(0),
            buf,
            elem: PhantomData,
        }
    }
}

impl<E, B, I> Vec<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    /// Returns the number of elements the vector can hold.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Returns the number of elements in the vector, also referred to as its 'length'.
    #[inline]
    pub fn len(&self) -> usize {
        self.len.into_usize()
    }

    #[inline]
    fn set_len(&mut self, new_len: I) {
        debug_assert!(new_len.into_usize() <= self.capacity());
        self.len = new_len;
    }

    /// Returns `true` if the vector contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len.into_usize() == 0
    }

    /// Returns `true` if the vector contains the maximum number of elements.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len.into_usize() == self.buf.capacity()
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
    pub fn pop(&mut self) -> Option<E> {
        if self.is_empty() {
            return None;
        }

        self.len = I::from_usize(self.len() - 1);
        unsafe { Some(self.buf.storage()[self.len()].as_ptr().read()) }
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// Equivalent to `&s[..]`.
    #[inline]
    pub fn as_slice(&self) -> &[E] {
        self
    }

    /// Extracts a mutable slice of the entire vector.
    ///
    /// Equivalent to `&mut s[..]`.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [E] {
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
    pub fn get(&self, index: I) -> Option<&E> {
        let index = index.into_usize();
        if self.len() <= index {
            return None;
        }

        unsafe { Some(self.buf.storage()[index].as_ptr().as_ref().unwrap()) }
    }

    /// Returns a mutable reference to the element at the specified index, or
    /// [`None`] if the index is out of bounds.
    #[inline]
    pub fn get_mut(&mut self, index: I) -> Option<&mut E> {
        let index = index.into_usize();
        if self.len() <= index {
            return None;
        }

        unsafe { Some(self.buf.storage_mut()[index].as_mut_ptr().as_mut().unwrap()) }
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
    pub fn try_push(&mut self, value: E) -> Result<(), E> {
        if self.is_full() {
            return Err(value);
        }

        let len = self.len();
        let p = self.buf.storage_mut()[len].as_mut_ptr();
        unsafe {
            p.write(value);
        }

        self.len = I::from_usize(len + 1);
        Ok(())
    }

    /// Appends an element to the back of the vector.
    ///
    /// # Panics
    /// Panics if the vector is already at capacity. See [`try_push`](Vec::try_push)
    /// for a checked version that never panics.
    #[inline]
    pub fn push(&mut self, value: E) {
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
        let new_len = len.into_usize();
        let old_len = self.len.into_usize();

        if new_len >= old_len {
            return;
        }

        for i in new_len..old_len {
            unsafe {
                self.buf.storage_mut()[i].as_mut_ptr().drop_in_place();
            }
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
    /// Pancis if either argument is out of bounds.
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
        let fst = fst.into_usize();
        let snd = snd.into_usize();
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
    pub fn swap_remove(&mut self, index: I) -> E {
        #[cold]
        #[inline(never)]
        fn assert_failed(idx: usize, len: usize) -> ! {
            panic!(
                "swap_remove index (is {}) should be < len (is {})",
                idx, len
            );
        }

        let idx = index.into_usize();
        let len = self.len.into_usize();
        if idx >= len {
            assert_failed(idx, len);
        }

        unsafe {
            let last = ptr::read(self.buf.storage()[len - 1].as_ptr());
            let hole = self.buf.storage_mut()[idx].as_mut_ptr();
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
    pub fn insert(&mut self, index: I, element: E) {
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
    pub fn try_insert(&mut self, index: I, element: E) -> Result<(), E> {
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

        let idx = index.into_usize();
        let len = self.len.into_usize();
        if idx > len {
            assert_failed(idx, len);
        }

        unsafe {
            let p = self.buf.storage_mut()[idx].as_mut_ptr();
            ptr::copy(p, p.offset(1), len - idx);
            ptr::write(p, element);
        }

        self.len = I::from_usize(len + 1);
        Ok(())
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
    pub fn remove(&mut self, index: I) -> E {
        #[cold]
        #[inline(never)]
        fn assert_failed(idx: usize, len: usize) -> ! {
            panic!("removal index (is {}) should be < len (is {})", idx, len);
        }

        let idx = index.into_usize();
        let len = self.len.into_usize();
        if idx >= len {
            assert_failed(idx, len);
        }

        unsafe {
            let ret;
            {
                let p = self.buf.storage_mut()[idx].as_mut_ptr();
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
        F: FnMut(&E) -> bool,
    {
        let len = self.len.into_usize();
        let mut del = 0;
        unsafe {
            for idx in 0..len {
                let p = self.buf.storage_mut()[idx].as_mut_ptr();
                if !f(p.as_mut().unwrap()) {
                    del += 1;
                } else if del > 0 {
                    ptr::swap(p, p.sub(del))
                }
            }
        }
        if del > 0 {
            self.truncate(I::from_usize(len - del));
        }
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
    pub fn drain<'a, R: RangeBounds<I>>(&'a mut self, range: R) -> Drain<'a, E, B, I> {
        use core::ops::Bound;
        let start = match range.start_bound() {
            Bound::Included(x) => x.into_usize(),
            Bound::Excluded(x) => x.into_usize().saturating_add(1),
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(x) => x.into_usize().saturating_add(1),
            Bound::Excluded(x) => x.into_usize(),
            Bound::Unbounded => 0,
        };
        assert!(
            start <= self.len(),
            "Vec::drain Illegal range, {} to {}",
            start,
            end
        );
        assert!(
            end <= self.len(),
            "Vec::drain Range ends at {} but length is only {}",
            end,
            self.len()
        );
        Drain {
            parent: self,
            target_start: start,
            front_index: start,
            back_index: end,
            target_end: end,
        }
    }
}

impl<E, B, I> core::ops::Deref for Vec<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    type Target = [E];
    fn deref(&self) -> &[E] {
        unsafe {
            core::slice::from_raw_parts(self.buf.storage()[0].as_ptr(), self.len.into_usize())
        }
    }
}

impl<E, B, I> core::ops::DerefMut for Vec<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn deref_mut(&mut self) -> &mut [E] {
        unsafe {
            core::slice::from_raw_parts_mut(
                self.buf.storage_mut()[0].as_mut_ptr(),
                self.len.into_usize(),
            )
        }
    }
}

impl<E, B, I> core::ops::Index<I> for Vec<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    type Output = E;
    fn index(&self, index: I) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<E, B, I> core::ops::IndexMut<I> for Vec<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.get_mut(index).unwrap()
    }
}

macro_rules! _impl_idx_range {
    ($self:ident, $idx:ident: $r:ty, $lo:expr, $hi:expr) => {
        impl<E, B, I> core::ops::Index<$r> for Vec<E, B, I>
        where
            B: ContiguousStorage<E>,
            I: Capacity + PartialOrd,
        {
            type Output = [E];
            #[allow(unused_variables)]
            fn index(&self, $idx: $r) -> &Self::Output {
                let $self = self;
                let start = $lo;
                let end = $hi;
                &self.as_slice()[start..end]
            }
        }

        impl<E, B, I> core::ops::IndexMut<$r> for Vec<E, B, I>
        where
            B: ContiguousStorage<E>,
            I: Capacity + PartialOrd,
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

_impl_idx_range! { s, index: core::ops::Range<I>, index.start.into_usize(), index.end.into_usize() }
_impl_idx_range! { s, index: core::ops::RangeFrom<I>, index.start.into_usize(), s.len() }
_impl_idx_range! { s, index: core::ops::RangeFull, 0, s.len() }
_impl_idx_range! { s, index: core::ops::RangeInclusive<I>, index.start().into_usize(), index.end().into_usize().saturating_add(1) }
_impl_idx_range! { s, index: core::ops::RangeTo<I>, 0, index.end.into_usize() }
_impl_idx_range! { s, index: core::ops::RangeToInclusive<I>, 0, index.end.into_usize().saturating_add(1) }

impl<E, B, I> core::convert::AsRef<[E]> for Vec<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn as_ref(&self) -> &[E] {
        self
    }
}

impl<E, B, I> core::convert::AsMut<[E]> for Vec<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn as_mut(&mut self) -> &mut [E] {
        self
    }
}

impl<E, B, I> core::ops::Drop for Vec<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                self.buf.storage_mut()[0].as_mut_ptr(),
                self.len(),
            ))
        }
    }
}

impl<E, B, I> core::fmt::Debug for Vec<E, B, I>
where
    E: core::fmt::Debug,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<E, B, I> Hash for Vec<E, B, I>
where
    E: Hash,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

impl<AE, AB, AI, BE, BB, BI> core::cmp::PartialEq<Vec<BE, BB, BI>> for Vec<AE, AB, AI>
where
    AE: core::cmp::PartialEq<BE>,
    AB: ContiguousStorage<AE>,
    BB: ContiguousStorage<BE>,
    AI: Capacity,
    BI: Capacity,
{
    #[inline]
    fn eq(&self, other: &Vec<BE, BB, BI>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<E, B, I> core::cmp::Eq for Vec<E, B, I>
where
    E: core::cmp::Eq,
    B: ContiguousStorage<E>,
    I: Capacity,
{
}

impl<V, E, B, I> core::cmp::PartialEq<&[V]> for Vec<E, B, I>
where
    E: core::cmp::PartialEq<V>,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    #[inline]
    fn eq(&self, other: &&[V]) -> bool {
        self.as_slice() == &other[..]
    }
}

impl<V, E, B, I> core::cmp::PartialEq<&mut [V]> for Vec<E, B, I>
where
    E: core::cmp::PartialEq<V>,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    #[inline]
    fn eq(&self, other: &&mut [V]) -> bool {
        self.as_slice() == &other[..]
    }
}

impl<V, E, B, I> core::cmp::PartialEq<Vec<E, B, I>> for &[V]
where
    V: core::cmp::PartialEq<E>,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    #[inline]
    fn eq(&self, other: &Vec<E, B, I>) -> bool {
        &self[..] == other.as_slice()
    }
}

impl<V, E, B, I> core::cmp::PartialEq<Vec<E, B, I>> for &mut [V]
where
    V: core::cmp::PartialEq<E>,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    #[inline]
    fn eq(&self, other: &Vec<E, B, I>) -> bool {
        &self[..] == other.as_slice()
    }
}

impl<E, B, I> core::cmp::PartialOrd for Vec<E, B, I>
where
    E: core::cmp::PartialOrd,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}

impl<E, B, I> core::cmp::Ord for Vec<E, B, I>
where
    E: core::cmp::Ord,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_slice().cmp(&other.as_slice())
    }
}

impl<E, B, Idx> core::iter::Extend<E> for Vec<E, B, Idx>
where
    B: ContiguousStorage<E>,
    Idx: Capacity,
{
    fn extend<I: core::iter::IntoIterator<Item = E>>(&mut self, iter: I) {
        for element in iter {
            self.push(element);
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
pub struct IntoIterator<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    start: I,
    end: I,
    buf: B,
    elems: PhantomData<E>,
}

impl<E, B, I> Iterator for IntoIterator<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    type Item = E;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.end.into_usize() - self.start.into_usize();
        (size, Some(size))
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let start = self.start.into_usize();
        let end = self.end.into_usize();
        if start >= end {
            return None;
        }

        let ret = unsafe { self.buf.storage()[start].as_ptr().read() };
        self.start = I::from_usize(start + 1);

        Some(ret)
    }
}

impl<E, B, I> core::iter::DoubleEndedIterator for IntoIterator<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let start = self.start.into_usize();
        let end = self.end.into_usize();
        if start >= end {
            return None;
        }

        let end = end - 1;
        let ret = unsafe { self.buf.storage()[end].as_ptr().read() };
        self.end = I::from_usize(end);

        Some(ret)
    }
}

impl<E, B, I> core::iter::ExactSizeIterator for IntoIterator<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
}

impl<E, B, I> core::iter::FusedIterator for IntoIterator<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
}

impl<E, B, I> Drop for IntoIterator<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn drop(&mut self) {
        self.for_each(drop);
    }
}

impl<E, B, I> IntoIter for Vec<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    type Item = E;
    type IntoIter = IntoIterator<E, B, I>;

    fn into_iter(mut self) -> Self::IntoIter {
        let end = self.len;
        #[allow(clippy::uninit_assumed_init)]
        let buf = core::mem::replace(&mut self.buf, unsafe {
            MaybeUninit::uninit().assume_init()
        });
        core::mem::forget(self);

        IntoIterator {
            start: I::from_usize(0),
            end,
            buf,
            elems: PhantomData,
        }
    }
}

impl<'a, E, B, I> IntoIter for &'a Vec<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    type Item = &'a E;
    type IntoIter = core::slice::Iter<'a, E>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

impl<'a, E, B, I> IntoIter for &'a mut Vec<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    type Item = &'a mut E;
    type IntoIter = core::slice::IterMut<'a, E>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_mut_slice().iter_mut()
    }
}

/// A draining iterator for `Vec<T>`.
///
/// This `struct` is created by [`Vec::drain`]. See its documentation for more.
pub struct Drain<'p, E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    parent: &'p mut Vec<E, B, I>,
    target_start: usize,
    front_index: usize,
    back_index: usize,
    target_end: usize,
}

impl<'p, E, B, I> core::iter::Iterator for Drain<'p, E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    type Item = E;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.back_index - self.front_index;
        (size, Some(size))
    }

    fn next(&mut self) -> Option<Self::Item> {
        if self.front_index != self.back_index {
            let out = unsafe { self.parent.as_slice().as_ptr().add(self.front_index).read() };
            self.front_index += 1;
            Some(out)
        } else {
            None
        }
    }
}

impl<'p, E, B, I> core::iter::DoubleEndedIterator for Drain<'p, E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.front_index != self.back_index {
            self.back_index -= 1;
            unsafe { Some(self.parent.as_slice().as_ptr().add(self.back_index).read()) }
        } else {
            None
        }
    }
}

impl<'p, E, B, I> core::iter::ExactSizeIterator for Drain<'p, E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
}

impl<'p, E, B, I> core::iter::FusedIterator for Drain<'p, E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
}

impl<'p, E, B, I> Drop for Drain<'p, E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn drop(&mut self) {
        self.for_each(drop);
        let count = self.target_end - self.target_start;
        let targets = &mut self.parent.as_mut_slice()[self.target_start..];
        targets.rotate_left(count);

        let new_len = I::from_usize(self.parent.len() - count);
        self.parent.set_len(new_len);
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
/// A vector using a heap-allocated slice for storage.
pub type HeapVec<E, I = usize> = Vec<E, crate::storage::HeapStorage<E>, I>;

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<E, I> HeapVec<E, I>
where
    E: Copy,
    I: Capacity,
{
    /// Constructs a new, empty `HeapVec<E, I>` with the specified capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        I::from_usize(capacity); // panics if I cannot index the whole slice

        Vec {
            len: I::from_usize(0),
            buf: alloc::vec![MaybeUninit::uninit(); capacity].into_boxed_slice(),
            elem: PhantomData,
        }
    }
}

/// A vector using an inline array for storage.
#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
pub type ArrayVec<E, const C: usize> = Vec<E, crate::storage::InlineStorage<E, C>, usize>;

/// A vector using an inline array for storage, generic over the index type.
#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
pub type TiArrayVec<E, Index, const C: usize> = Vec<E, crate::storage::InlineStorage<E, C>, Index>;

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
impl<E, I, const C: usize> Vec<E, [MaybeUninit<E>; C], I>
where
    I: Capacity,
{
    /// Constructs a new, empty `Vec` backed by an inline array.
    ///
    /// # Examples
    /// ```
    /// let vec = coca::ArrayVec::<u32, 6>::new();
    /// assert_eq!(vec.capacity(), 6);
    /// assert_eq!(vec.len(), 0);
    /// ```
    #[inline]
    pub fn new() -> Self {
        I::from_usize(C); // panics if I cannot index the whole array

        Vec {
            len: I::from_usize(0),
            buf: unsafe { MaybeUninit::uninit().assume_init() },
            elem: PhantomData,
        }
    }
}

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
impl<E, I, const C: usize> Default for Vec<E, [MaybeUninit<E>; C], I>
where
    I: Capacity,
{
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
impl<E, I, const C: usize> core::clone::Clone for Vec<E, [MaybeUninit<E>; C], I>
where
    E: Clone,
    I: Capacity,
{
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

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
impl<E, I, const C: usize> From<&[E]> for Vec<E, [MaybeUninit<E>; C], I>
where
    E: Clone,
    I: Capacity,
{
    fn from(source: &[E]) -> Self {
        I::from_usize(C); // panics if I cannot index the whole array
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

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
impl<E, I, const C: usize> From<&mut [E]> for Vec<E, [MaybeUninit<E>; C], I>
where
    E: Clone,
    I: Capacity,
{
    fn from(source: &mut [E]) -> Self {
        I::from_usize(C); // panics if I cannot index the whole array
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

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
impl<V, E, B, I, const N: usize> core::cmp::PartialEq<Vec<E, B, I>> for [V; N]
where
    V: core::cmp::PartialEq<E>,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    #[inline]
    fn eq(&self, other: &Vec<E, B, I>) -> bool {
        &self[..] == other.as_slice()
    }
}

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
impl<V, E, B, I, const N: usize> core::cmp::PartialEq<[V; N]> for Vec<E, B, I>
where
    E: core::cmp::PartialEq<V>,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    #[inline]
    fn eq(&self, other: &[V; N]) -> bool {
        self.as_slice() == &other[..]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes_of_instantiated_types() {
        use core::mem::size_of;

        assert_eq!(size_of::<SliceVec<u64, usize>>(), 3 * size_of::<usize>());
        assert_eq!(size_of::<ArenaVec<u64, usize>>(), 3 * size_of::<usize>());

        #[cfg(feature = "alloc")]
        assert_eq!(size_of::<HeapVec<u64, usize>>(), 3 * size_of::<usize>());

        #[cfg(feature = "nightly")]
        {
            assert_eq!(size_of::<ArrayVec<u8, 8>>(), size_of::<usize>() + 8);
            assert_eq!(size_of::<TiArrayVec<u8, u8, 99>>(), 100);
            assert_eq!(
                size_of::<Vec<u32, &mut [MaybeUninit<u32>; 1000], usize>>(),
                2 * size_of::<usize>()
            );
        }
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
    }
}
