//! A double-ended queue implemented with a ring buffer.
//!
//! This queue has O(1) inserts and removals from both ends of the sequence.
//! It also has O(1) indexing like a vector.

use core::fmt::{self, Debug, Formatter};
use core::hash::{Hash, Hasher};
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::ops::{Index, IndexMut, Range};

use crate::storage::{
    buffer_too_large_for_index_type, mut_ptr_at_index, normalize_range, ptr_at_index, ArrayLike, Capacity, Storage,
};
use crate::vec::Vec;

/// A double-ended queue implemented with a ring buffer.
///
/// The "default" usage of this type as a queue is to use [`push_back`](Deque::push_back)
/// to add to the queue, and [`pop_front`](Deque::pop_front) to remove from it.
///
/// Since `Deque` is a ring buffer, its elements are not necessarily contiguous
/// in memory. If you want to access the elements as a single slice, such as for
/// efficient sorting, you can use [`make_contiguous`](Deque::make_contiguous).
/// It rotates the `Deque` so that its elements do not wrap, and returns a
/// mutable slice to the now contiguous element sequence.
///
/// `Deque` is designed to work with any capacity between 2 and `usize::max_value() / 2`
/// (inclusive). As such, almost all indexing operations are implemented as
/// `storage[(offset + index) % capacity]`; you may therefore observe disproportionate
/// performance benefits when the capacity is known at compile time, especially
/// with powers of 2, which allow this expression to be optimized to
/// `storage[(offset + index) & (CAPACITY - 1)]`.
pub struct Deque<T, S: Storage<ArrayLike<T>>, I: Capacity> {
    front: I,
    len: I,
    buf: S,
    elem: PhantomData<T>,
}

/// A double-ended queue using any mutable slice for storage.
///
/// # Examples
/// ```
/// use core::mem::MaybeUninit;
/// let mut backing_array = [MaybeUninit::<char>::uninit(); 32];
/// let (slice1, slice2) = (&mut backing_array[..]).split_at_mut(16);
/// let mut deque1 = coca::SliceDeque::<_>::from(slice1);
/// let mut deque2 = coca::SliceDeque::<_>::from(slice2);
/// assert_eq!(deque1.capacity(), 16);
/// assert_eq!(deque2.capacity(), 16);
/// ```
pub type SliceDeque<'a, T, I = usize> = Deque<T, crate::storage::SliceStorage<'a, T>, I>;
/// A double-ended queue using an arena-allocated slice for storage.
///
/// See [`Arena::try_deque`](crate::Arena::try_deque) for example usage.
pub type ArenaDeque<'a, T, I = usize> = Deque<T, crate::storage::ArenaStorage<'a, ArrayLike<T>>, I>;

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> From<S> for Deque<T, S, I> {
    /// Converts a contiguous block of memory into an empty deque.
    ///
    /// # Panics
    /// This may panic if the index type I cannot represent `buf.capacity()`.
    fn from(buf: S) -> Self {
        if buf.capacity() > I::MAX_REPRESENTABLE {
            buffer_too_large_for_index_type::<I>();
        }

        Deque {
            front: I::from_usize(0),
            len: I::from_usize(0),
            buf,
            elem: PhantomData,
        }
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> From<Vec<T, S, I>> for Deque<T, S, I> {
    fn from(vec: Vec<T, S, I>) -> Self {
        let (buf, len) = vec.into_raw_parts();
        Deque {
            front: I::from_usize(0),
            len,
            buf,
            elem: PhantomData,
        }
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> Deque<T, S, I> {
    /// Decomposes a `Deque<T, S, I>` into its raw parts.
    ///
    /// Returns the raw storage type, the front offset and the length of the
    /// deque in elements. These are the same arguments in the same order as
    /// the arguments to [`from_raw_parts`](Deque::from_raw_parts).
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 3];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_front(1);
    /// deque.push_back(2);
    /// let (buf, front, len) = deque.into_raw_parts();
    /// unsafe {
    ///     assert_eq!(buf[2].assume_init(), 1);
    ///     assert_eq!(buf[0].assume_init(), 2);
    ///     // buf[1] is uninitialized
    /// }
    /// ```
    pub fn into_raw_parts(self) -> (S, I, I) {
        let ptr = &self.buf as *const S;
        let result = (unsafe { ptr.read() }, self.front, self.len);
        core::mem::forget(self);
        result
    }

    /// Creates a `Deque<T, S, I>` directly from its raw parts.
    ///
    /// # Safety
    /// Callers must ensure that the first `length` values after `front`
    /// (modulo `buf.capacity()`) are initialized, and that `front` and
    /// `length` are both less than or equal to `buf.capacity()`.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 3];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_front(1);
    /// deque.push_back(2);
    ///
    /// let (buf, front, len) = deque.into_raw_parts();
    /// let deque = unsafe { coca::SliceDeque::from_raw_parts(buf, front, len) };
    /// assert_eq!(deque, &[1, 2]);
    /// ```
    pub unsafe fn from_raw_parts(buf: S, front: I, length: I) -> Self {
        Deque {
            front,
            len: length,
            buf,
            elem: PhantomData,
        }
    }

    /// Returns the number of elements the deque can hold.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Returns the number of elements currently in the deque.
    #[inline]
    pub fn len(&self) -> usize {
        self.len.as_usize()
    }

    /// Returns `true` exactly when the deque contains zero elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len.as_usize() == 0
    }

    /// Returns `true` exactly when the deque contains the maximum number of elements.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len.as_usize() == self.buf.capacity()
    }

    /// Returns `true` if the `Deque` contains an element equal to the given value.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 3];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(0);
    /// deque.push_back(1);
    /// assert_eq!(deque.contains(&1), true);
    /// assert_eq!(deque.contains(&10), false);
    /// ```
    pub fn contains(&self, x: &T) -> bool
    where
        T: PartialEq,
    {
        let (a, b) = self.as_slices();
        a.contains(x) || b.contains(x)
    }

    #[inline(always)]
    fn physical_index_unchecked(&self, index: I) -> usize {
        let index = index.as_usize();
        (self.front.as_usize() + index) % self.capacity()
    }

    #[inline(always)]
    fn physical_index(&self, index: I) -> Option<usize> {
        let index = index.as_usize();
        if index >= self.len() {
            return None;
        }

        Some((self.front.as_usize() + index) % self.capacity())
    }

    fn storage_mut(&mut self) -> &mut [T] {
        unsafe {
            core::slice::from_raw_parts_mut(self.buf.get_mut_ptr().cast::<T>(), self.capacity())
        }
    }

    /// Returns a reference to the element at the given index, or [`None`] if
    /// the index is out of bounds.
    ///
    /// The element at index 0 is the front of the queue.
    #[inline]
    pub fn get(&self, index: I) -> Option<&T> {
        let index = self.physical_index(index)?;
        unsafe { Some(ptr_at_index(&self.buf, index).as_ref().unwrap()) }
    }

    /// Returns a mutable reference to the element at the given index, or [`None`]
    /// if the index is out of bounds.
    ///
    /// The element at index 0 is the front of the queue.
    #[inline]
    pub fn get_mut(&mut self, index: I) -> Option<&mut T> {
        let index = self.physical_index(index)?;
        unsafe { Some(mut_ptr_at_index(&mut self.buf, index).as_mut().unwrap()) }
    }

    /// Returns a reference to the front element, or [`None`] if the `Deque` is empty.
    #[inline]
    pub fn front(&self) -> Option<&T> {
        self.get(I::from_usize(0))
    }

    /// Returns a mutable reference to the front element, or [`None`] if the `Deque` is empty.
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.get_mut(I::from_usize(0))
    }

    /// Returns a reference to the back element, or [`None`] if the `Deque` is empty.
    #[inline]
    pub fn back(&self) -> Option<&T> {
        self.get(I::from_usize(self.len() - 1))
    }

    /// Returns a mutable reference to the back element, or [`None`] if the `Deque is empty.
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.get_mut(I::from_usize(self.len() - 1))
    }

    /// Removes the first element and returns it, or [`None`] if the `Deque` is empty.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 3];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// assert_eq!(deque.pop_front(), Some(1));
    /// assert_eq!(deque.pop_front(), Some(2));
    /// assert_eq!(deque.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        let front = self.front.as_usize();
        let result = unsafe { ptr_at_index(&self.buf, front).read() };
        self.front = I::from_usize(front + 1 % self.capacity());
        self.len = I::from_usize(self.len() - 1);

        Some(result)
    }

    /// Removes the last element and returns it, or [`None`] if the `Deque` is empty.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 3];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(1);
    /// deque.push_back(3);
    /// assert_eq!(deque.pop_back(), Some(3));
    /// assert_eq!(deque.pop_back(), Some(1));
    /// assert_eq!(deque.pop_back(), None);
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        let idx = (self.front.as_usize() + self.len() - 1) % self.capacity();
        let result = unsafe { ptr_at_index(&self.buf, idx).read() };
        self.len = I::from_usize(self.len() - 1);

        Some(result)
    }

    /// Prepends an element to the front of the `Deque`, returning `Err(value)`
    /// if it is already full.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 3];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// assert!(deque.try_push_front(1).is_ok());
    /// assert!(deque.try_push_front(2).is_ok());
    /// assert!(deque.try_push_front(3).is_ok());
    /// assert_eq!(deque.try_push_front(4), Err(4));
    /// ```
    pub fn try_push_front(&mut self, value: T) -> Result<(), T> {
        if self.is_full() {
            return Err(value);
        }

        let idx = (self.front.as_usize() + self.capacity() - 1) % self.capacity();
        let ptr = mut_ptr_at_index(&mut self.buf, idx);
        unsafe {
            ptr.write(value);
        }

        self.front = I::from_usize(idx);
        self.len = I::from_usize(self.len() + 1);

        Ok(())
    }

    /// Prepends an element to the front of the `Deque`.
    ///
    /// # Panics
    /// Panics if the deque is already at capacity. See [`try_push_front`](Deque::try_push_front)
    /// for a checked variant that never panics.
    pub fn push_front(&mut self, value: T) {
        if self.try_push_front(value).is_err() {
            panic!("deque is already at capacity")
        }
    }

    /// Appends an element to the back of the `Deque`, returning `Err(value)`
    /// if it is already full.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 3];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// assert!(deque.try_push_back(1).is_ok());
    /// assert!(deque.try_push_back(2).is_ok());
    /// assert!(deque.try_push_back(3).is_ok());
    /// assert_eq!(deque.try_push_back(4), Err(4));
    /// ```
    pub fn try_push_back(&mut self, value: T) -> Result<(), T> {
        if self.is_full() {
            return Err(value);
        }

        let end = self.physical_index_unchecked(self.len);
        let ptr = mut_ptr_at_index(&mut self.buf, end);
        unsafe {
            ptr.write(value);
        }

        self.len = I::from_usize(self.len() + 1);

        Ok(())
    }

    /// Appends an element to the back of the `Deque`.
    ///
    /// # Panics
    /// Panics if the deque is already at capacity. See [`try_push_back`](Deque::try_push_back)
    /// for a checked variant that never panics.
    pub fn push_back(&mut self, value: T) {
        if self.try_push_back(value).is_err() {
            panic!("deque is already at capacity")
        }
    }

    /// Shortens the `Deque`, keeping the first `len` elements and dropping the rest.
    ///
    /// If `len` is greater than the deque's current length, this has no effect.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 4];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(5);
    /// deque.push_back(10);
    /// deque.push_back(15);
    /// assert_eq!(deque.as_slices(), (&[5, 10, 15][..], &[][..]));
    /// deque.truncate(1);
    /// assert_eq!(deque.as_slices(), (&[5][..], &[][..]));
    /// ```
    pub fn truncate(&mut self, len: I) {
        let new_len = len.as_usize();
        let old_len = self.len();

        if new_len >= old_len {
            return;
        }

        for i in new_len..old_len {
            let idx = i % self.capacity();
            let ptr = self.buf.get_mut_ptr().cast::<T>();
            unsafe {
                ptr.add(idx).drop_in_place();
            }
        }

        self.len = len;
    }

    /// Clears the `Deque`, dropping all values.
    pub fn clear(&mut self) {
        self.truncate(I::from_usize(0));
        self.front = I::from_usize(0);
    }

    /// Swaps the elements at indices `i` and `j`.
    ///
    /// `i` and `j` may be equal.
    ///
    /// The element at index 0 is the front of the queue.
    ///
    /// # Panics
    /// Panics if either index is out of bounds.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 4];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(2);
    /// deque.push_back(1);
    /// deque.push_front(3);
    /// deque.swap(0, 2);
    /// assert_eq!(deque, &[1, 2, 3]);
    /// ```
    pub fn swap(&mut self, i: I, j: I) {
        let i = self
            .physical_index(i)
            .expect("index `i` is out of bounds in `swap`");
        let j = self
            .physical_index(j)
            .expect("index `j` is out of bounds in `swap`");
        self.storage_mut().swap(i, j);
    }

    /// Removes an element from anywhere in the `Deque` and returns it, replacing
    /// it with the front element.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// Returns [`None`] if `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 4];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// assert_eq!(deque.swap_remove_front(2), Some(3));
    /// assert_eq!(deque, &[2, 1]);
    /// ```
    pub fn swap_remove_front(&mut self, index: I) -> Option<T> {
        let index = self.physical_index(index)?;
        let front = self.front.as_usize();

        unsafe {
            let last = ptr_at_index(&self.buf, front).read();
            let hole = mut_ptr_at_index(&mut self.buf, index);
            self.len = I::from_usize(self.len() - 1);
            self.front = I::from_usize((front + 1) % self.capacity());
            Some(hole.replace(last))
        }
    }

    /// Removes an element from anywhere in the `Deque` and returns it,
    /// replacing it with the back element.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// Returns [`None`] if `index` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 4];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// assert_eq!(deque.swap_remove_back(0), Some(1));
    /// assert_eq!(deque, &[3, 2]);
    /// ```
    pub fn swap_remove_back(&mut self, index: I) -> Option<T> {
        let index = self.physical_index(index)?;
        let back = (self.front.as_usize() + self.len() - 1) % self.capacity();

        unsafe {
            let last = ptr_at_index(&self.buf, back).read();
            let hole = mut_ptr_at_index(&mut self.buf, index);
            self.len = I::from_usize(self.len() - 1);
            Some(hole.replace(last))
        }
    }

    /// Inserts an element at `index` within the `Deque`, returning `Err(value)`
    /// if it is full.
    ///
    /// Whichever end is closer to the insertion point will be moved to make
    /// room, and all elements in between will be shifted to new positions.
    ///
    /// The element at index 0 is the front of the queue.
    ///
    /// # Panics
    /// Panics if `index` is greater than the deque's length.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<char>::uninit(); 4];
    /// let mut deque = coca::SliceDeque::<char>::from(&mut backing_region[..]);
    /// deque.push_back('a');
    /// deque.push_back('b');
    /// deque.push_back('c');
    /// assert_eq!(deque, &['a', 'b', 'c']);
    ///
    /// assert!(deque.try_insert(1, 'd').is_ok());
    /// assert_eq!(deque, &['a', 'd', 'b', 'c']);
    /// ```
    pub fn try_insert(&mut self, index: I, value: T) -> Result<(), T> {
        if self.is_full() {
            return Err(value);
        }

        let index = index.as_usize();
        if index > self.len() {
            panic!("index out of bounds in `try_insert`");
        }

        let cap = self.capacity();
        let front = self.front.as_usize();
        let back = front + self.len();

        // count back == cap as discontiguous to handle spill-over correctly
        let contiguous = back < self.capacity();

        let distance_to_front = index;
        let distance_to_back = self.len() - index;
        let move_front = distance_to_front < distance_to_back;

        let new_front = if move_front {
            (front + self.capacity() - 1) % self.capacity()
        } else {
            front
        };

        let index_wrapped = new_front + index >= self.capacity();

        match (contiguous, move_front, index_wrapped) {
            (true, true, _) => {
                // storage is contiguous, insertion point is in lower half
                // -> shift all elements before the insertion point to the left by one
                if distance_to_front > 0 {
                    let dst = mut_ptr_at_index(&mut self.buf, new_front);
                    let src = ptr_at_index(&self.buf, front);
                    unsafe { core::ptr::copy(src, dst, 1); }

                    let dst = mut_ptr_at_index(&mut self.buf, front);
                    let src = ptr_at_index(&self.buf, front + 1);
                    unsafe { core::ptr::copy(src, dst, distance_to_front - 1); }
                }

                let ptr = mut_ptr_at_index(&mut self.buf, (new_front + index) % cap);
                unsafe { ptr.write(value); }
            }
            (true, false, _) => {
                // storage is contiguous, insertion point is in upper half
                // -> shift all elements after the insertion point to the right by one
                let physical_index = front + index;
                let src = ptr_at_index(&self.buf, physical_index);
                let dst = mut_ptr_at_index(&mut self.buf, physical_index + 1);
                unsafe { core::ptr::copy(src, dst, distance_to_back); }
                let ptr = mut_ptr_at_index(&mut self.buf, physical_index);
                unsafe { ptr.write(value); }
            }
            (false, true, false) => {
                // storage is not contiguous, insertion point is in lower half and does not wrap
                // -> shift all elements before the insertion point to the left by one
                let ptr = mut_ptr_at_index(&mut self.buf, new_front);
                unsafe {
                    ptr.write(value);
                }
                self.storage_mut()[new_front..].rotate_left(1);
            }
            (false, false, true) => {
                // storage is not contiguous, insertion point is in upper half and does wrap
                // -> shift all elements after the insertion point to the right by one
                let physical_index = (front + index) % self.capacity();
                let ptr = mut_ptr_at_index(&mut self.buf, physical_index + distance_to_back);
                unsafe {
                    ptr.write(value);
                }
                self.storage_mut()[physical_index..=physical_index + distance_to_back]
                    .rotate_right(1);
            }
            (false, true, true) => {
                // storage is not contiguous, insertion point is in the lower half, but the index wraps
                // -> shift all elements before the insertion point to the left by one, accounting for wrap
                let physical_index = (new_front + index) % self.capacity();
                let ptr = mut_ptr_at_index(&mut self.buf, 0);
                let tmp = unsafe { ptr.replace(value) };
                self.storage_mut()[..=physical_index].rotate_left(1);

                let ptr = mut_ptr_at_index(&mut self.buf, new_front);
                unsafe {
                    ptr.write(tmp);
                }
                self.storage_mut()[new_front..].rotate_left(1);
            }
            (false, false, false) => {
                // storage is not contiguous, insertion point is in the upper half, but the index doesn't wrap
                // -> shift all elements after the insertion point to the right by one, accounting for wrap
                let physical_index = (front + index) % cap;
                let ptr = mut_ptr_at_index(&mut self.buf, cap - 1);
                let tmp = unsafe { ptr.replace(value) };
                self.storage_mut()[physical_index..].rotate_right(1);

                let back = back % cap;
                let ptr = mut_ptr_at_index(&mut self.buf, back);
                unsafe {
                    ptr.write(tmp);
                }
                self.storage_mut()[..=back].rotate_right(1);
            }
        }

        self.len = I::from_usize(self.len() + 1);
        self.front = I::from_usize(new_front);
        Ok(())
    }

    /// Inserts an element at `index` within the `Deque`.
    ///
    /// Whichever end is closer to the insertion point will be moved to make
    /// room, and all elements in between will be shifted to new positions.
    ///
    /// The element at index 0 is the front of the queue.
    ///
    /// # Panics
    /// Panics if `index` is greater than the deque's length, or if the deque
    /// is already at capacity. See [`try_insert`](Deque::try_insert) for a
    /// checked version.
    pub fn insert(&mut self, index: I, value: T) {
        if self.try_insert(index, value).is_err() {
            panic!("deque is already at capacity");
        }
    }

    /// Removes and returns the element at `index` from the `Deque`, or [`None`]
    /// if `index` is out of bounds.
    ///
    /// Whichever end is closer to the removal point will be moved to fill the
    /// gap, and all affected elements will be shifted to new positions.
    ///
    /// The element at index 0 is the front of the queue.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 4];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// assert_eq!(deque.remove(1), Some(2));
    /// assert_eq!(deque, &[1, 3]);
    /// ```
    pub fn remove(&mut self, index: I) -> Option<T> {
        let index = index.as_usize();
        if index >= self.len() {
            return None;
        }

        let cap = self.capacity();
        let front = self.front.as_usize();
        let back = front + self.len();
        let contiguous = back <= cap;

        let distance_to_front = index;
        let distance_to_back = self.len() - index - 1;
        let move_front = distance_to_front < distance_to_back;

        let index_wrapped = front + index >= cap;
        let physical_index = (front + index) % cap;

        let ptr = ptr_at_index(&self.buf, physical_index);
        let result = unsafe { ptr.read() };

        match (contiguous, move_front, index_wrapped) {
            (true, true, _) | (false, true, false) => {
                // Storage is contiguous, index is in lower half
                // OR Storage is discontiguous, index is in lower half, and does not wrap
                // -> shift all elements before the index to the right
                unsafe {
                    let src = ptr_at_index(&self.buf, front);
                    let dst = mut_ptr_at_index(&mut self.buf, front + 1);
                    core::ptr::copy(src, dst, distance_to_front);
                }

                self.front = I::from_usize((front + 1) % cap);
            }
            (true, false, _) | (false, false, true) => {
                // Storage is contiguous, index is in upper half
                // OR Storage is discontiguous, index is in upper half, and does wrap
                // -> shift all elements after the index to the left
                unsafe {
                    let src = ptr_at_index(&self.buf, physical_index + 1);
                    let dst = mut_ptr_at_index(&mut self.buf, physical_index);
                    core::ptr::copy(src, dst, distance_to_back);
                }
            }
            (false, true, true) => {
                // Storage is discontiguous, index is in lower half, but also wraps
                // -> shift all elements before the index to the right, accounting for wrap
                unsafe {
                    let src = self.buf.get_ptr().cast::<T>();
                    let dst = mut_ptr_at_index(&mut self.buf, 1);
                    core::ptr::copy(src, dst, physical_index);

                    let src = ptr_at_index(&self.buf, cap - 1);
                    let dst = self.buf.get_mut_ptr().cast::<T>();
                    core::ptr::copy(src, dst, 1);

                    let src = ptr_at_index(&self.buf, front);
                    let dst = mut_ptr_at_index(&mut self.buf, front + 1);
                    core::ptr::copy(src, dst, cap - front - 1);
                }

                self.front = I::from_usize((front + 1) % cap);
            }
            (false, false, false) => {
                // Storage is discontiguous, index is in upper half, but doesn't wrap
                // -> shift all elements after the index to the left, accounting for wrap
                unsafe {
                    let src = ptr_at_index(&self.buf, physical_index + 1);
                    let dst = mut_ptr_at_index(&mut self.buf, physical_index);
                    core::ptr::copy(src, dst, cap - physical_index - 1);

                    let src = self.buf.get_ptr().cast::<T>();
                    let dst = mut_ptr_at_index(&mut self.buf, cap - 1);
                    core::ptr::copy(src, dst, 1);

                    let src = ptr_at_index(&self.buf, 1);
                    let dst = self.buf.get_mut_ptr().cast::<T>();
                    core::ptr::copy(src, dst, back % cap - 1);
                }
            }
        }

        self.len = I::from_usize(self.len() - 1);
        Some(result)
    }

    /// Places an element at position `index` within the `Deque`, returning the
    /// element previously stored there.
    ///
    /// # Panics
    /// Panics if `index` is greater than or equal to the deque's length.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 4];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(4);
    /// assert_eq!(deque.replace(2, 3), 4);
    /// assert_eq!(deque, &[1, 2, 3]);
    /// ```
    pub fn replace(&mut self, index: I, value: T) -> T {
        let index = self
            .physical_index(index)
            .expect("index out of bounds in `replace`");
        unsafe { mut_ptr_at_index(&mut self.buf, index).replace(value) }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 4];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// deque.push_back(4);
    /// deque.retain(|&x| x % 2 == 0);
    /// assert_eq!(deque, &[2, 4]);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        let capacity = self.capacity();
        let old_len = self.len();
        let mut new_len = 0;

        for i in 0..old_len {
            let idx = i % capacity;
            let src = ptr_at_index(&self.buf, idx);
            let retain = f(unsafe { src.as_ref().unwrap() });

            if retain {
                let dst = mut_ptr_at_index(&mut self.buf, new_len % capacity);
                unsafe { core::ptr::copy(src, dst, 1); }
                new_len += 1;
            } else {
                let to_drop = mut_ptr_at_index(&mut self.buf, idx);
                unsafe { core::ptr::drop_in_place(to_drop); }
            }
        }

        self.len = I::from_usize(new_len);
    }

    fn rotate_left_inner(&mut self, mid: usize) {
        debug_assert!(mid * 2 <= self.len());

        let cap = self.capacity();
        let front = self.front.as_usize();
        let back = front + self.len();
        let contiguous = back <= cap;

        let first_count = if contiguous {
            // storage is contiguous, use the first copy to (at most) fill the right gap
            usize::min(cap - back, mid)
        } else {
            // storage is discontiguous, use the first copy to (at most) shift over the right section
            usize::min(cap - front, mid)
        };

        let src = ptr_at_index(&self.buf, front);
        let dst = mut_ptr_at_index(&mut self.buf, back % cap);
        unsafe { core::ptr::copy(src, dst, first_count); }

        let src = ptr_at_index(&self.buf, (front + first_count) % cap);
        let dst = mut_ptr_at_index(&mut self.buf, (back + first_count) % cap);
        unsafe { core::ptr::copy(src, dst, mid - first_count); }

        self.front = I::from_usize((front + mid) % cap);
    }

    fn rotate_right_inner(&mut self, k: usize) {
        debug_assert!(k * 2 <= self.len());

        let cap = self.capacity();
        let front = self.front.as_usize();
        let back = front + self.len();
        let contiguous = back <= cap;

        let first_count = if contiguous {
            // storage is contiguous, use the first copy to (at most) fill the left gap
            usize::min(front, k)
        } else {
            // storage is discontiguous, use the first copy to (at most) shift over the left section
            usize::min(back % cap, k)
        };

        let src = ptr_at_index(&self.buf, (back - first_count) % cap);
        let dst = mut_ptr_at_index(&mut self.buf, (front + cap - first_count) % cap);
        unsafe { core::ptr::copy(src, dst, first_count); }

        let src = ptr_at_index(&self.buf, (back + cap - k) % cap);
        let dst = mut_ptr_at_index(&mut self.buf, (front + cap - k) % cap);
        unsafe { core::ptr::copy(src, dst, k - first_count); }

        self.front = I::from_usize((front + cap - k) % cap);
    }

    /// Rotates the `Deque` `mid` places to the left.
    ///
    /// Equivalently,
    ///
    /// * Rotates `mid` into the first position.
    /// * Pops the first `mid` items and pushes them to the end.
    /// * Rotates `len() - mid` places to the right.
    ///
    /// # Panics
    /// Panics if `mid` is greater than the deque's length. Note that
    /// `mid == len()` does *not* panic and is a no-op rotation.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 16];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// for x in 0..10 { deque.push_back(x); }
    /// for i in 1..10 {
    ///     deque.rotate_left(3);
    ///     assert_eq!(deque.front(), Some(&(i * 3 % 10)));
    /// }
    /// deque.rotate_left(3);
    /// assert_eq!(deque, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    /// ```
    pub fn rotate_left(&mut self, mid: I) {
        let mid = mid.as_usize();
        assert!(mid <= self.len());
        let k = self.len() - mid;
        if mid <= k {
            self.rotate_left_inner(mid);
        } else {
            self.rotate_right_inner(k);
        }
    }

    /// Rotates the `Deque` `k` places to the right.
    ///
    /// Equivalently,
    ///
    /// * Rotates the first item into position `k`.
    /// * Pops the last `k` items and pushes them to the front.
    /// * Rotates `len() - k` places to the left.
    ///
    /// # Panics
    /// Panics if `k` is greater than the deque's length. Note that `k == len()`
    /// does *not* panic and is a no-op rotation.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 16];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// for x in 0..10 { deque.push_back(x); }
    /// for i in 1..10 {
    ///     deque.rotate_right(3);
    ///     assert_eq!(deque.get(i * 3 % 10), Some(&0));
    /// }
    /// deque.rotate_right(3);
    /// assert_eq!(deque, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    /// ```
    pub fn rotate_right(&mut self, k: I) {
        let k = k.as_usize();
        assert!(k <= self.len());
        let mid = self.len() - k;
        if k <= mid {
            self.rotate_right_inner(k);
        } else {
            self.rotate_left_inner(mid);
        }
    }

    /// Returns a pair of slices which contain, in order, the contents of the `Deque`.
    ///
    /// If [`make_contiguous`](Deque::make_contiguous) was previously called,
    /// all elements of the deque will be in the first slice and the second
    /// slice will be empty.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 4];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(2);
    /// deque.push_back(1);
    /// deque.push_front(3);
    /// assert_eq!(deque.as_slices(), (&[3][..], &[2, 1][..]));
    /// ```
    pub fn as_slices(&self) -> (&[T], &[T]) {
        let front = self.front.as_usize();
        let back = front + self.len();
        let ptr = self.buf.get_ptr().cast::<T>();
        if back <= self.capacity() {
            let slice = unsafe { core::slice::from_raw_parts(ptr.add(front), self.len()) };
            (slice, &[])
        } else {
            let fst =
                unsafe { core::slice::from_raw_parts(ptr.add(front), self.capacity() - front) };
            let snd =
                unsafe { core::slice::from_raw_parts(ptr, self.len() - (self.capacity() - front)) };
            (fst, snd)
        }
    }

    /// Returns a pair of mutable slices which contain, in order, the contents
    /// of the `Deque`.
    ///
    /// If [`make_contiguous`](Deque::make_contiguous) was previously called,
    /// all elements of the deque will be in the first slice and the second
    /// slice will be empty.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 4];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(2);
    /// deque.push_back(1);
    /// deque.push_front(3);
    /// deque.as_mut_slices().0[0] = 1;
    /// deque.as_mut_slices().1[1] = 3;
    /// assert_eq!(deque.as_slices(), (&[1][..], &[2, 3][..]));
    /// ```
    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
        let front = self.front.as_usize();
        let back = front + self.len();
        if back <= self.capacity() {
            let ptr = self.buf.get_mut_ptr().cast::<T>();
            let slice = unsafe { core::slice::from_raw_parts_mut(ptr.add(front), self.len()) };
            (slice, &mut [])
        } else {
            let len = self.len();
            let cap = self.capacity();

            let storage = self.storage_mut();
            let (rest, fst) = storage.split_at_mut(front);
            let (snd, _) = rest.split_at_mut(len - (cap - front));

            let fst = unsafe {
                let ptr = fst.as_mut_ptr().cast::<T>();
                core::slice::from_raw_parts_mut(ptr, fst.len())
            };
            let snd = unsafe {
                let ptr = snd.as_mut_ptr().cast::<T>();
                core::slice::from_raw_parts_mut(ptr, snd.len())
            };

            (fst, snd)
        }
    }

    /// Rearranges the internal storage of the `Deque` so it is one contiguous
    /// slice, which is then returned.
    ///
    /// This does not change the order of the inserted elements. As it returns
    /// a mutable slice, this can be used to sort or binary search a deque.
    ///
    /// Once the internal storage is contiguous, the [`as_slices`](Deque::as_slices)
    /// and [`as_mut_slices`](Deque::as_mut_slices) methods will return the
    /// entire contents of the `Deque` in a single slice.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 4];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(2);
    /// deque.push_back(1);
    /// assert_eq!(deque, &[2, 1]);
    ///
    /// deque.push_front(3);
    /// assert_eq!(deque, &[3, 2, 1]);
    /// ```
    pub fn make_contiguous(&mut self) -> &mut [T] {
        let front = self.front.as_usize();
        let back = front + self.len();
        if back <= self.capacity() {
            let ptr = self.buf.get_mut_ptr().cast::<T>();
            unsafe { core::slice::from_raw_parts_mut(ptr.add(front), self.len()) }
        } else {
            self.storage_mut().rotate_left(front);
            self.front = I::from_usize(0);

            let ptr = self.buf.get_mut_ptr().cast::<T>();
            unsafe { core::slice::from_raw_parts_mut(ptr, self.len()) }
        }
    }

    /// Returns a front-to-back iterator.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 4];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(5);
    /// deque.push_back(3);
    /// deque.push_back(4);
    ///
    /// let mut it = deque.iter();
    /// assert_eq!(it.next(), Some(&5));
    /// assert_eq!(it.next(), Some(&3));
    /// assert_eq!(it.next(), Some(&4));
    /// assert!(it.next().is_none());
    /// ```
    pub fn iter(&self) -> Iter<'_, T, S, I> {
        Iter {
            front: self.front,
            len: self.len,
            buf: &self.buf,
            _ref: PhantomData,
        }
    }

    /// Returns a front-to-back iterator that returns mutable references.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 4];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.push_back(5);
    /// deque.push_back(3);
    /// deque.push_back(4);
    /// for num in deque.iter_mut() {
    ///     *num = *num - 2;
    /// }
    /// assert_eq!(deque, &[3, 1, 2]);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, T, S, I> {
        IterMut {
            front: self.front,
            len: self.len,
            buf: &mut self.buf,
            _ref: PhantomData,
        }
    }

    /// Creates an iterator that covers the specified range in the `Deque`.
    ///
    /// # Panics
    /// Panics if the starting point is greater than the end point or if the
    /// end point is greater than the length of the deque.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 8];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.extend(1..=5);
    /// assert_eq!(deque, &[1, 2, 3, 4, 5]);
    ///
    /// let mut it = deque.range(2..4);
    /// assert_eq!(it.next(), Some(&3));
    /// assert_eq!(it.next(), Some(&4));
    /// assert!(it.next().is_none());
    /// ```
    pub fn range<R: core::ops::RangeBounds<I>>(&self, range: R) -> Iter<'_, T, S, I> {
        let Range { start, end } = normalize_range(range, self.len());
        Iter {
            front: I::from_usize((self.front.as_usize() + start) % self.capacity()),
            len: I::from_usize(end - start),
            buf: &self.buf,
            _ref: PhantomData,
        }
    }

    /// Creates a mutable iterator that covers the specified range in the `Deque`.
    ///
    /// # Panics
    /// Panics if the starting point is greater than the end point or if the
    /// end point is greater than the length of the deque.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 8];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.extend(1..=5);
    /// assert_eq!(deque, &[1, 2, 3, 4, 5]);
    ///
    /// deque.range_mut(2..4).for_each(|x| *x *= 2);
    /// assert_eq!(deque, &[1, 2, 6, 8, 5]);
    /// ```
    pub fn range_mut<R: core::ops::RangeBounds<I>>(&mut self, range: R) -> IterMut<'_, T, S, I> {
        let Range { start, end } = normalize_range(range, self.len());
        IterMut {
            front: I::from_usize((self.front.as_usize() + start) % self.capacity()),
            len: I::from_usize(end - start),
            buf: &mut self.buf,
            _ref: PhantomData,
        }
    }

    /// Creates a draining iterator that removes the specified range in the
    /// deque and yields the removed items.
    ///
    /// When the iterator **is** dropped, all elements in the range are removed
    /// from the deque, even if the iterator was not fully consumed. If the
    /// iterator **is not** dropped (with [`core::mem::forget`] for example),
    /// it is unspecified how many elements are removed.
    ///
    /// # Panics
    /// Panics if the starting point is greater than the end point or if the end
    /// point is greater than the length of the deque.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 8];
    /// let mut deque = coca::SliceDeque::<i32>::from(&mut backing_region[..]);
    /// deque.extend(1..=5);
    ///
    /// let mut drained = deque.drain(2..4);
    /// assert_eq!(drained.next(), Some(3));
    /// assert_eq!(drained.next(), Some(4));
    /// assert!(drained.next().is_none());
    ///
    /// drop(drained);
    /// assert_eq!(deque, [1, 2, 5]);
    ///
    /// // A full range clears the deque
    /// deque.drain(..);
    /// assert!(deque.is_empty());
    /// ```
    pub fn drain<R: core::ops::RangeBounds<I>>(&mut self, range: R) -> Drain<'_, T, S, I> {
        let Range { start, end } = normalize_range(range, self.len());

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
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> Index<I> for Deque<T, S, I> {
    type Output = T;

    #[inline]
    fn index(&self, index: I) -> &T {
        self.get(index).expect("out of bounds access")
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> IndexMut<I> for Deque<T, S, I> {
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut T {
        self.get_mut(index).expect("out of bounds access")
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> Drop for Deque<T, S, I> {
    fn drop(&mut self) {
        let (front, back) = self.as_mut_slices();
        let front_ptr = front.as_mut_ptr();
        let back_ptr = back.as_mut_ptr();
        unsafe {
            core::ptr::slice_from_raw_parts_mut(front_ptr, front.len()).drop_in_place();
            core::ptr::slice_from_raw_parts_mut(back_ptr, back.len()).drop_in_place();
        }
    }
}

impl<T: Debug, S: Storage<ArrayLike<T>>, I: Capacity> Debug for Deque<T, S, I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let (front, back) = self.as_slices();
        f.debug_list().entries(front).entries(back).finish()
    }
}

impl<T: Hash, S: Storage<ArrayLike<T>>, I: Capacity> Hash for Deque<T, S, I> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        let (front, back) = self.as_slices();
        Hash::hash_slice(front, state);
        Hash::hash_slice(back, state);
    }
}

impl<AT, AS, AI, BT, BS, BI> PartialEq<Deque<BT, BS, BI>> for Deque<AT, AS, AI>
where
    AT: PartialEq<BT>,
    AS: Storage<ArrayLike<AT>>,
    BS: Storage<ArrayLike<BT>>,
    AI: Capacity,
    BI: Capacity,
{
    fn eq(&self, other: &Deque<BT, BS, BI>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        let (self_front, self_back) = self.as_slices();
        let (other_front, other_back) = other.as_slices();

        match self_front.len() {
            len if len == other_front.len() => self_front == other_front && self_back == other_back,
            len if len < other_front.len() => {
                let a = self_front.len();
                let b = other_front.len() - a;
                debug_assert_eq!(self_back[..b].len(), other_front[a..].len());
                debug_assert_eq!(self_back[b..].len(), other_back.len());
                self_front == &other_front[..a]
                    && self_back[..b] == other_front[a..]
                    && &self_back[b..] == other_back
            }
            _ => {
                let a = other_front.len();
                let b = self_front.len() - a;
                debug_assert_eq!(self_front[a..].len(), other_back[..b].len());
                debug_assert_eq!(self_back.len(), other_back[b..].len());
                &self_front[..a] == other_front
                    && self_front[a..] == other_back[..b]
                    && self_back == &other_back[b..]
            }
        }
    }
}

impl<T: Eq, S: Storage<ArrayLike<T>>, I: Capacity> Eq for Deque<T, S, I> {}

impl<T: PartialEq, S: Storage<ArrayLike<T>>, I: Capacity, R: AsRef<[T]>> PartialEq<R>
    for Deque<T, S, I>
{
    fn eq(&self, other: &R) -> bool {
        let other = other.as_ref();
        if self.len() != other.len() {
            return false;
        }

        let (front, back) = self.as_slices();
        let mid = front.len();
        front == &other[..mid] && back == &other[mid..]
    }
}

impl<T, AS, AI, BS, BI> PartialOrd<Deque<T, BS, BI>> for Deque<T, AS, AI>
where
    T: PartialOrd,
    AS: Storage<ArrayLike<T>>,
    BS: Storage<ArrayLike<T>>,
    AI: Capacity,
    BI: Capacity,
{
    fn partial_cmp(&self, other: &Deque<T, BS, BI>) -> Option<core::cmp::Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord, S: Storage<ArrayLike<T>>, I: Capacity> Ord for Deque<T, S, I> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> Extend<T> for Deque<T, S, I> {
    fn extend<It: IntoIterator<Item = T>>(&mut self, iter: It) {
        iter.into_iter().for_each(|item| self.push_back(item));
    }
}

impl<'a, T: 'a + Clone, S: Storage<ArrayLike<T>>, I: Capacity> Extend<&'a T> for Deque<T, S, I> {
    fn extend<It: IntoIterator<Item = &'a T>>(&mut self, iter: It) {
        iter.into_iter()
            .for_each(|item| self.push_back(item.clone()));
    }
}

/// An iterator over the elements of a deque.
///
/// This `struct` is created by the [`iter`](Deque::iter) method on [`Deque`].
/// See its documentation for more.
pub struct Iter<'a, T: 'a, S: Storage<ArrayLike<T>>, I: Capacity> {
    front: I,
    len: I,
    buf: &'a S,
    _ref: PhantomData<&'a T>,
}

impl<'a, T: 'a + Debug, S: Storage<ArrayLike<T>>, I: Capacity> Debug for Iter<'a, T, S, I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let (front, back) = {
            let front = self.front.as_usize();
            let back = front + self.len.as_usize();

            if back <= self.buf.capacity() {
                unsafe {
                    (
                        core::slice::from_raw_parts(
                            ptr_at_index(self.buf, front),
                            self.len.as_usize(),
                        ),
                        &[][..],
                    )
                }
            } else {
                unsafe {
                    (
                        core::slice::from_raw_parts(
                            ptr_at_index(self.buf, front),
                            self.buf.capacity() - front,
                        ),
                        core::slice::from_raw_parts(
                            ptr_at_index(self.buf, 0),
                            back - self.buf.capacity(),
                        ),
                    )
                }
            }
        };

        f.debug_tuple("Iter").field(&front).field(&back).finish()
    }
}

impl<'a, T: 'a, S: Storage<ArrayLike<T>>, I: Capacity> Iterator for Iter<'a, T, S, I> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        let len = self.len.as_usize();
        if len == 0 {
            return None;
        }

        let front = self.front.as_usize();
        self.front = I::from_usize((front + 1) % self.buf.capacity());
        self.len = I::from_usize(len - 1);
        let result = unsafe { ptr_at_index(self.buf, front).as_ref() };
        debug_assert!(result.is_some());
        result
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len.as_usize();
        (len, Some(len))
    }
}

impl<'a, T: 'a, S: Storage<ArrayLike<T>>, I: Capacity> DoubleEndedIterator for Iter<'a, T, S, I> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a T> {
        let len = self.len.as_usize();
        if len == 0 {
            return None;
        }

        let front = self.front.as_usize();
        let idx = (front + len - 1) % self.buf.capacity();
        self.len = I::from_usize(len - 1);
        let result = unsafe { ptr_at_index(self.buf, idx).as_ref() };
        debug_assert!(result.is_some());
        result
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> ExactSizeIterator for Iter<'_, T, S, I> {}
impl<T, S: Storage<ArrayLike<T>>, I: Capacity> FusedIterator for Iter<'_, T, S, I> {}

/// A mutable iterator over the elements of a deque.
///
/// This `struct` is created by the [`iter_mut`](Deque::iter_mut) method on [`Deque`].
/// See its documentation for more.
pub struct IterMut<'a, T: 'a, S: Storage<ArrayLike<T>>, I: Capacity> {
    front: I,
    len: I,
    buf: &'a mut S,
    _ref: PhantomData<&'a mut T>,
}

impl<'a, T: 'a + Debug, S: Storage<ArrayLike<T>>, I: Capacity> Debug for IterMut<'a, T, S, I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> fmt::Result {
        let (front, back) = {
            let front = self.front.as_usize();
            let back = front + self.len.as_usize();

            if back <= self.buf.capacity() {
                unsafe {
                    (
                        core::slice::from_raw_parts(
                            ptr_at_index(&self.buf, front),
                            self.len.as_usize(),
                        ),
                        &[][..],
                    )
                }
            } else {
                unsafe {
                    (
                        core::slice::from_raw_parts(
                            ptr_at_index(&self.buf, front),
                            self.buf.capacity() - front,
                        ),
                        core::slice::from_raw_parts(
                            ptr_at_index(&self.buf, 0),
                            back - self.buf.capacity(),
                        ),
                    )
                }
            }
        };

        f.debug_tuple("Iter").field(&front).field(&back).finish()
    }
}

impl<'a, T: 'a, S: Storage<ArrayLike<T>>, I: Capacity> Iterator for IterMut<'a, T, S, I> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<&'a mut T> {
        let len = self.len.as_usize();
        if len == 0 {
            return None;
        }

        let front = self.front.as_usize();
        self.front = I::from_usize((front + 1) % self.buf.capacity());
        self.len = I::from_usize(len - 1);
        let result = unsafe { mut_ptr_at_index(&mut self.buf, front).as_mut() };
        debug_assert!(result.is_some());
        result
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len.as_usize();
        (len, Some(len))
    }
}

impl<'a, T: 'a, S: Storage<ArrayLike<T>>, I: Capacity> DoubleEndedIterator
    for IterMut<'a, T, S, I>
{
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut T> {
        let len = self.len.as_usize();
        if len == 0 {
            return None;
        }

        let front = self.front.as_usize();
        let idx = (front + len - 1) % self.buf.capacity();
        self.len = I::from_usize(len - 1);
        let result = unsafe { mut_ptr_at_index(&mut self.buf, idx).as_mut() };
        debug_assert!(result.is_some());
        result
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> ExactSizeIterator for IterMut<'_, T, S, I> {}
impl<T, S: Storage<ArrayLike<T>>, I: Capacity> FusedIterator for IterMut<'_, T, S, I> {}

/// An owning iterator over the elements of a deque.
///
/// This `struct` is created by the [`into_iter`](Deque::into_iter) method on
/// [`Deque`] (provided by the `IntoIterator` trait). See its documentation for
/// more.
pub struct IntoIter<T, S: Storage<ArrayLike<T>>, I: Capacity> {
    inner: Deque<T, S, I>,
}

impl<T: Debug, S: Storage<ArrayLike<T>>, I: Capacity> Debug for IntoIter<T, S, I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IntoIterator").field(&self.inner).finish()
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> Iterator for IntoIter<T, S, I> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.inner.pop_front()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.inner.len();
        (len, Some(len))
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> DoubleEndedIterator for IntoIter<T, S, I> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.inner.pop_back()
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> ExactSizeIterator for IntoIter<T, S, I> {}
impl<T, S: Storage<ArrayLike<T>>, I: Capacity> FusedIterator for IntoIter<T, S, I> {}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> IntoIterator for Deque<T, S, I> {
    type Item = T;
    type IntoIter = IntoIter<T, S, I>;

    /// Converts the `Deque` into a front-to-back iterator yielding elements by value.
    fn into_iter(self) -> IntoIter<T, S, I> {
        IntoIter { inner: self }
    }
}

impl<'a, T, S: Storage<ArrayLike<T>>, I: Capacity> IntoIterator for &'a Deque<T, S, I> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T, S, I>;

    fn into_iter(self) -> Iter<'a, T, S, I> {
        self.iter()
    }
}

impl<'a, T, S: Storage<ArrayLike<T>>, I: Capacity> IntoIterator for &'a mut Deque<T, S, I> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T, S, I>;

    fn into_iter(self) -> IterMut<'a, T, S, I> {
        self.iter_mut()
    }
}

/// A draining iterator over the elements of a deque.
///
/// This `struct` is created by the [`drain`](Deque::drain) method on [`Deque`].
/// See its documentation for more.
pub struct Drain<'p, T, S: Storage<ArrayLike<T>>, I: Capacity> {
    parent: &'p mut Deque<T, S, I>,
    original_len: usize,
    target_start: usize,
    front_index: usize,
    back_index: usize,
    target_end: usize,
}

impl<T: Debug, S: Storage<ArrayLike<T>>, I: Capacity> Debug for Drain<'_, T, S, I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain")
            .field(&self.target_start)
            .field(&self.target_end)
            .field(
                &self
                    .parent
                    .range(I::from_usize(self.front_index)..I::from_usize(self.back_index)),
            )
            .finish()
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> Iterator for Drain<'_, T, S, I> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        if self.front_index == self.back_index {
            return None;
        }

        let idx = (self.parent.front.as_usize() + self.front_index) % self.parent.capacity();
        self.front_index += 1;

        unsafe { Some(ptr_at_index(&self.parent.buf, idx).read()) }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.back_index - self.front_index;
        (len, Some(len))
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> DoubleEndedIterator for Drain<'_, T, S, I> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        if self.back_index == self.front_index {
            return None;
        }

        let idx = (self.parent.front.as_usize() + self.back_index - 1) % self.parent.capacity();
        self.back_index -= 1;

        unsafe { Some(ptr_at_index(&self.parent.buf, idx).read()) }
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> ExactSizeIterator for Drain<'_, T, S, I> {}
impl<T, S: Storage<ArrayLike<T>>, I: Capacity> FusedIterator for Drain<'_, T, S, I> {}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> Drop for Drain<'_, T, S, I> {
    fn drop(&mut self) {
        // 1. drop any items that remain untaken
        let cap = self.parent.capacity();
        let front = self.parent.front.as_usize() + self.front_index;
        let back = self.parent.front.as_usize() + self.back_index;

        if front >= cap || back <= cap {
            // remaining items are contiguous, drop as single slice
            let ptr = mut_ptr_at_index(&mut self.parent.buf, front % cap);
            unsafe { core::ptr::slice_from_raw_parts_mut(ptr, back - front).drop_in_place(); }
        } else {
            // remaining items are discontiguous, account for wrapping
            let ptr = mut_ptr_at_index(&mut self.parent.buf, front);
            let len = cap - front;
            unsafe { core::ptr::slice_from_raw_parts_mut(ptr, len).drop_in_place(); }

            let ptr = mut_ptr_at_index(&mut self.parent.buf, 0);
            let len = (back - front) - len;
            unsafe { core::ptr::slice_from_raw_parts_mut(ptr, len).drop_in_place(); }
        }

        // 2. choose which portion of the unaffected items to shift over to close the gap
        let front = self.parent.front.as_usize();
        let back = front + self.original_len;
        let target_start = front + self.target_start;
        let target_end = front + self.target_end;
        let target_wrapped = target_start <= cap && cap <= target_end;

        let distance_to_front = self.target_start;
        let distance_to_back = self.original_len - self.target_end;
        let move_front = distance_to_front < distance_to_back;
        let source_wrapped = if move_front {
            front < cap && cap < target_start
        } else {
            target_end < cap && cap < back
        };

        match (move_front, target_wrapped, source_wrapped) {
            (false, false, false) => {
                // wrap point is outside relevant range, move back in one copy
                let src = ptr_at_index(&self.parent.buf, target_end % cap);
                let dst = mut_ptr_at_index(&mut self.parent.buf, target_start % cap);
                unsafe { core::ptr::copy(src, dst, distance_to_back); }
            }
            (true, false, false) => {
                // wrap point is outside relevant range, move front in one copy
                let new_front = target_end - distance_to_front;
                self.parent.front = I::from_usize(new_front);

                let src = ptr_at_index(&self.parent.buf, front);
                let dst = mut_ptr_at_index(&mut self.parent.buf, new_front);
                unsafe { core::ptr::copy(src, dst, distance_to_front); }
            }
            (false, true, false) => {
                // wrap point is inside target range, move back in two copies
                let fst_count = usize::min(cap - target_start, distance_to_back);
                let src = ptr_at_index(&self.parent.buf, target_end % cap);
                let dst = mut_ptr_at_index(&mut self.parent.buf, target_start % cap);
                unsafe { core::ptr::copy(src, dst, fst_count); }

                let dst_idx = (target_start + fst_count) % cap;
                let src = ptr_at_index(&self.parent.buf, (target_end + fst_count) % cap);
                let dst = mut_ptr_at_index(&mut self.parent.buf, dst_idx);
                unsafe { core::ptr::copy(src, dst, distance_to_back - fst_count); }
            }
            (true, true, false) => {
                // wrap point is inside target range, move front in two copies
                let fst_count = usize::min(target_end - cap, distance_to_front);
                let src = ptr_at_index(&self.parent.buf, target_start - fst_count);
                let dst = mut_ptr_at_index(&mut self.parent.buf, (target_end - fst_count) % cap);
                unsafe { core::ptr::copy(src, dst, fst_count); }

                let new_front = (target_end - distance_to_front) % cap;
                self.parent.front = I::from_usize(new_front);

                let src = ptr_at_index(&self.parent.buf, front);
                let dst = mut_ptr_at_index(&mut self.parent.buf, new_front);
                unsafe { core::ptr::copy(src, dst, distance_to_front - fst_count); }
            }
            (false, false, true) => {
                // wrap point is inside source range, move back in three copies
                let fst_count = cap - target_end;
                let src = ptr_at_index(&self.parent.buf, target_end);
                let dst = mut_ptr_at_index(&mut self.parent.buf, target_start);
                unsafe { core::ptr::copy(src, dst, fst_count); }

                let remaining = distance_to_back - fst_count;
                let snd_count = usize::min(cap - (target_start + fst_count), remaining);
                let src = ptr_at_index(&self.parent.buf, 0);
                let dst = mut_ptr_at_index(&mut self.parent.buf, target_start + fst_count);
                unsafe { core::ptr::copy(src, dst, snd_count); }

                let remaining = remaining - snd_count;
                let src = ptr_at_index(&self.parent.buf, snd_count);
                let dst = mut_ptr_at_index(&mut self.parent.buf, 0);
                unsafe { core::ptr::copy(src, dst, remaining); }
            }
            (true, false, true) => {
                // wrap point is inside source range, move front in three copies
                let fst_count = target_start - cap;
                let src = ptr_at_index(&self.parent.buf, 0);
                let dst = mut_ptr_at_index(&mut self.parent.buf, target_end - cap - fst_count);
                unsafe { core::ptr::copy(src, dst, fst_count); }

                let remaining = distance_to_front - fst_count;
                let snd_count = usize::min(target_end - cap - fst_count, remaining);
                let dst_idx = target_end - cap - (fst_count + snd_count);

                let src = ptr_at_index(&self.parent.buf, cap - snd_count);
                let dst = mut_ptr_at_index(&mut self.parent.buf, dst_idx);
                unsafe { core::ptr::copy(src, dst, snd_count); }

                let new_front = (front + (target_end - target_start)) % cap;
                self.parent.front = I::from_usize(new_front);

                let remaining = remaining - snd_count;
                let src = ptr_at_index(&self.parent.buf, front);
                let dst = mut_ptr_at_index(&mut self.parent.buf, new_front);
                unsafe { core::ptr::copy(src, dst, remaining); }
            }
            (_, true, true) => {
                // wrap point cannot be in both the source and target ranges!
                unreachable!();
            }
        }

        self.parent.len = I::from_usize(self.original_len - (target_end - target_start));
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
/// A deque using a heap-allocated slice for storage.
///
/// Note that this still has a fixed capacity, and will never reallocate.
///
/// # Examples
/// ```
/// let mut deque = coca::AllocDeque::<char>::with_capacity(4);
/// deque.push_front('b');
/// deque.push_front('a');
/// deque.push_back('c');
/// deque.push_back('d');
/// assert_eq!(deque, &['a', 'b', 'c', 'd']);
/// assert_eq!(deque.try_push_back('e'), Err('e'));
/// ```
pub type AllocDeque<T, I = usize> = Deque<T, crate::storage::AllocStorage<ArrayLike<T>>, I>;

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<T: Copy, I: Capacity> AllocDeque<T, I> {
    /// Creates an empty `AllocDeque` with the specified capacity.
    ///
    /// # Panics
    /// Panics if `capacity` cannot be represented by the a `usize`.
    pub fn with_capacity(capacity: I) -> Self {
        let cap = capacity.as_usize();
        if capacity != I::from_usize(cap) {
            buffer_too_large_for_index_type::<I>();
        }

        Deque {
            front: I::from_usize(0),
            len: I::from_usize(0),
            buf: crate::storage::AllocStorage::with_capacity(cap),
            elem: PhantomData,
        }
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<T: Copy, I: Capacity> Clone for AllocDeque<T, I> {
    fn clone(&self) -> Self {
        let mut result = Self::with_capacity(I::from_usize(self.capacity()));
        result.extend(self.iter().cloned());
        result
    }
}

/// A deque using an inline array for storage.
///
/// # Examples
/// ```
/// let mut deque = coca::InlineDeque::<char, 4>::new();
/// deque.push_front('b');
/// deque.push_front('a');
/// deque.push_back('c');
/// deque.push_back('d');
/// assert_eq!(deque, &['a', 'b', 'c', 'd']);
/// assert_eq!(deque.try_push_back('e'), Err('e'));
/// ```
pub type InlineDeque<T, const C: usize> = Deque<T, crate::storage::InlineStorage<T, C>, usize>;

/// A deque using an inline array for storage, generic over the index type.
///
/// # Examples
/// ```
/// let mut deque = coca::TiInlineDeque::<char, u8, 4>::new();
/// deque.push_front('a');
/// assert_eq!(deque[0u8], 'a');
/// ```
pub type TiInlineDeque<T, I, const C: usize> = Deque<T, crate::storage::InlineStorage<T, C>, I>;

impl<T, I: Capacity, const C: usize> Deque<T, [core::mem::MaybeUninit<T>; C], I> {
    /// Constructs a new deque backed by an inline array.
    ///
    /// # Panics
    /// Panics if `C` cannot be represented as a value of type `I`.
    ///
    /// # Examples
    /// ```
    /// let deque = coca::InlineDeque::<u32, 7>::new();
    /// assert_eq!(deque.len(), 0);
    /// assert_eq!(deque.capacity(), 7);
    /// ```
    #[inline]
    pub fn new() -> Self {
        if C > I::MAX_REPRESENTABLE {
            buffer_too_large_for_index_type::<I>();
        }

        Deque {
            front: I::from_usize(0),
            len: I::from_usize(0),
            buf: unsafe { core::mem::MaybeUninit::uninit().assume_init() },
            elem: PhantomData,
        }
    }
}

impl<T, I: Capacity, const C: usize> Default for Deque<T, [core::mem::MaybeUninit<T>; C], I> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone, I: Capacity, const C: usize> Clone for Deque<T, [core::mem::MaybeUninit<T>; C], I> {
    fn clone(&self) -> Self {
        let mut ret = Self::new();
        ret.extend(self.iter().cloned());
        ret
    }

    fn clone_from(&mut self, source: &Self) {
        self.clear();
        self.extend(source.iter().cloned());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_insertion_cases() {
        let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 8];
        let mut deque = SliceDeque::<i32>::from(&mut backing_region[..]);

        deque.try_insert(0, 1).unwrap();
        assert_eq!(deque.as_slices(), (&[1][..], &[][..]));

        deque.try_insert(0, 2).unwrap();
        assert_eq!(deque.as_slices(), (&[2][..], &[1][..]));

        deque.try_insert(1, 3).unwrap();
        assert_eq!(deque.as_slices(), (&[2][..], &[3, 1][..]));

        deque.try_insert(1, 4).unwrap();
        assert_eq!(deque.as_slices(), (&[2, 4][..], &[3, 1][..]));

        deque.push_back(5);
        deque.push_back(6);
        deque.push_back(7);
        assert_eq!(deque.as_slices(), (&[2, 4][..], &[3, 1, 5, 6, 7][..]));

        deque.try_insert(3, 8).unwrap();
        assert_eq!(deque.as_slices(), (&[2, 4, 3][..], &[8, 1, 5, 6, 7][..]));

        deque.pop_back();
        deque.pop_back();
        deque.pop_back();
        deque.push_front(5);
        deque.push_front(6);
        assert_eq!(deque.as_slices(), (&[6, 5, 2, 4, 3][..], &[8, 1][..]));

        deque.try_insert(4, 7).unwrap();
        assert_eq!(deque.as_slices(), (&[6, 5, 2, 4, 7][..], &[3, 8, 1][..]));
    }

    #[test]
    fn all_removal_cases() {
        let mut backing_region = [core::mem::MaybeUninit::<i32>::uninit(); 8];
        let mut deque = SliceDeque::<i32>::from(&mut backing_region[..]);

        deque.push_back(1);
        deque.push_back(2);
        deque.push_back(3);
        deque.push_back(4);
        assert_eq!(deque.as_slices(), (&[1, 2, 3, 4][..], &[][..]));

        assert_eq!(deque.remove(2), Some(3));
        assert_eq!(deque.as_slices(), (&[1, 2, 4][..], &[][..]));

        deque.push_back(3);
        assert_eq!(deque.remove(1), Some(2));
        assert_eq!(deque.as_slices(), (&[1, 4, 3][..], &[][..]));

        deque.push_front(2);
        deque.push_front(5);
        deque.push_front(6);
        assert_eq!(deque.as_slices(), (&[6, 5][..], &[2, 1, 4, 3][..]));

        assert_eq!(deque.remove(3), Some(1));
        assert_eq!(deque.as_slices(), (&[6, 5][..], &[2, 4, 3][..]));

        deque.push_back(1);
        assert_eq!(deque.remove(2), Some(2));
        assert_eq!(deque.as_slices(), (&[6][..], &[5, 4, 3, 1][..]));

        for _ in 0..3 {
            let x = deque.pop_back().unwrap();
            deque.push_front(x);
        }

        assert_eq!(deque.as_slices(), (&[4, 3, 1, 6][..], &[5][..]));

        assert_eq!(deque.remove(3), Some(6));
        assert_eq!(deque.as_slices(), (&[4, 3, 1, 5][..], &[][..]));

        deque.push_back(2);
        deque.push_back(6);
        assert_eq!(deque.remove(1), Some(3));
        assert_eq!(deque.as_slices(), (&[4, 1, 5][..], &[2, 6][..]));
    }

    #[test]
    fn all_drain_cases() {
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

        for len in 1..=8 {
            for offset in 0..=len {
                for end in 1..=len {
                    for start in 0..end {
                        let drop_count = Cell::new(0);
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
                        let mut deque = SliceDeque::<Droppable>::from(&mut backing_region[..]);

                        for x in 0..offset {
                            deque.push_front(Droppable {
                                value: offset - x,
                                counter: &drop_count,
                            });
                        }
                        for x in offset..len {
                            deque.push_back(Droppable {
                                value: x,
                                counter: &drop_count,
                            });
                        }

                        deque.drain(start..end);
                        assert_eq!(deque.len(), len - (end - start));
                        assert_eq!(drop_count.get(), end - start);

                        drop(deque);
                        assert_eq!(drop_count.get(), len);
                    }
                }
            }
        }
    }
}
