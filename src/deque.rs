//! A double-ended queue implemented with a ring buffer.
//!
//! This queue has O(1) inserts and removals from both ends of the sequence.
//! It also has O(1) indexing like a vector.

use core::marker::PhantomData;

use crate::storage::{Capacity, ContiguousStorage};
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
pub struct Deque<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    front: I,
    len: I,
    buf: B,
    elem: PhantomData<E>,
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
pub type SliceDeque<'a, E, I = usize> = Deque<E, crate::storage::SliceStorage<'a, E>, I>;
/// A double-ended queue using an arena-allocated slice for storage.
pub type ArenaDeque<'a, E, I = usize> = Deque<E, crate::storage::ArenaStorage<'a, E>, I>;

impl<E, B, I> From<B> for Deque<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    /// Converts a contiguous block of memory into an empty deque.
    fn from(buf: B) -> Self {
        Deque {
            front: I::from_usize(0),
            len: I::from_usize(0),
            buf,
            elem: PhantomData,
        }
    }
}

impl<E, B: ContiguousStorage<E>, I: Capacity> From<Vec<E, B, I>> for Deque<E, B, I> {
    fn from(vec: Vec<E, B, I>) -> Self {
        let (buf, len) = vec.into_raw_parts();
        Deque {
            front: I::from_usize(0),
            len,
            buf,
            elem: PhantomData,
        }
    }
}

impl<E, B, I> Deque<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    /// Returns the number of elements the deque can hold.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Returns the number of elements currently in the deque.
    #[inline]
    pub fn len(&self) -> usize {
        self.len.into_usize()
    }

    /// Returns `true` exactly when the deque contains zero elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len.into_usize() == 0
    }

    /// Returns `true` exactly when the deque contains the maximum number of elements.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len.into_usize() == self.buf.capacity()
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
    pub fn contains(&self, x: &E) -> bool
    where
        E: PartialEq,
    {
        let (a, b) = self.as_slices();
        a.contains(x) || b.contains(x)
    }

    #[inline(always)]
    fn physical_index_unchecked(&self, index: I) -> usize {
        let index = index.into_usize();
        (self.front.into_usize() + index) % self.capacity()
    }

    #[inline(always)]
    fn physical_index(&self, index: I) -> Option<usize> {
        let index = index.into_usize();
        if index >= self.len() {
            return None;
        }

        Some((self.front.into_usize() + index) % self.capacity())
    }

    /// Returns a reference to the element at the given index, or [`None`] if
    /// the index is out of bounds.
    ///
    /// The element at index 0 is the front of the queue.
    #[inline]
    pub fn get(&self, index: I) -> Option<&E> {
        let index = self.physical_index(index)?;
        unsafe { Some(self.buf.get_ptr(index).as_ref().unwrap()) }
    }

    /// Returns a mutable reference to the element at the given index, or [`None`]
    /// if the index is out of bounds.
    ///
    /// The element at index 0 is the front of the queue.
    #[inline]
    pub fn get_mut(&mut self, index: I) -> Option<&mut E> {
        let index = self.physical_index(index)?;
        unsafe { Some(self.buf.get_mut_ptr(index).as_mut().unwrap()) }
    }

    /// Returns a reference to the front element, or [`None`] if the `Deque` is empty.
    #[inline]
    pub fn front(&self) -> Option<&E> {
        self.get(I::from_usize(0))
    }

    /// Returns a mutable reference to the front element, or [`None`] if the `Deque` is empty.
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut E> {
        self.get_mut(I::from_usize(0))
    }

    /// Returns a reference to the back element, or [`None`] if the `Deque` is empty.
    #[inline]
    pub fn back(&self) -> Option<&E> {
        self.get(I::from_usize(self.len() - 1))
    }

    /// Returns a mutable reference to teh back element, or [`None`] if the `Deque is empty.
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut E> {
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
    pub fn pop_front(&mut self) -> Option<E> {
        if self.is_empty() {
            return None;
        }

        let front = self.front.into_usize();
        let result = unsafe { self.buf.get_ptr(front).read() };
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
    pub fn pop_back(&mut self) -> Option<E> {
        if self.is_empty() {
            return None;
        }

        let idx = (self.front.into_usize() + self.len() - 1) % self.capacity();
        let result = unsafe { self.buf.get_ptr(idx).read() };
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
    pub fn try_push_front(&mut self, value: E) -> Result<(), E> {
        if self.is_full() {
            return Err(value);
        }

        let idx = (self.front.into_usize() + self.capacity() - 1) % self.capacity();
        let ptr = self.buf.get_mut_ptr(idx);
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
    /// for a checked variant that never pancis.
    pub fn push_front(&mut self, value: E) {
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
    pub fn try_push_back(&mut self, value: E) -> Result<(), E> {
        if self.is_full() {
            return Err(value);
        }

        let end = self.physical_index_unchecked(self.len);
        let ptr = self.buf.get_mut_ptr(end);
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
    /// for a checked variant that never pancis.
    pub fn push_back(&mut self, value: E) {
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
        let new_len = len.into_usize();
        let old_len = self.len();

        if new_len >= old_len {
            return;
        }

        for i in new_len..old_len {
            let idx = i % self.capacity();
            let ptr = self.buf.storage_mut().as_mut_ptr() as *mut E;
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
        self.buf.storage_mut().swap(i, j);
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
    pub fn swap_remove_front(&mut self, index: I) -> Option<E> {
        let index = self.physical_index(index)?;
        let front = self.front.into_usize();

        unsafe {
            let last = self.buf.get_ptr(front).read();
            let hole = self.buf.get_mut_ptr(index);
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
    pub fn swap_remove_back(&mut self, index: I) -> Option<E> {
        let index = self.physical_index(index)?;
        let back = (self.front.into_usize() + self.len() - 1) % self.capacity();

        unsafe {
            let last = self.buf.get_ptr(back).read();
            let hole = self.buf.get_mut_ptr(index);
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
    pub fn try_insert(&mut self, index: I, value: E) -> Result<(), E> {
        if self.is_full() {
            return Err(value);
        }

        let index = index.into_usize();
        if index > self.len() {
            panic!("index out of bounds in `try_insert`");
        }

        let cap = self.capacity();
        let front = self.front.into_usize();
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
                    let dst = self.buf.get_mut_ptr(new_front);
                    let src = self.buf.get_ptr(front);
                    unsafe { core::ptr::copy(src, dst, 1) };

                    let dst = self.buf.get_mut_ptr(front);
                    let src = self.buf.get_ptr(front + 1);
                    unsafe { core::ptr::copy(src, dst, distance_to_front - 1) };
                }

                let ptr = self.buf.get_mut_ptr((new_front + index) % cap);
                unsafe { ptr.write(value) };
            }
            (true, false, _) => {
                // storage is contiguous, insertion point is in upper half
                // -> shift all elements after the insertion point to the right by one
                let physical_index = front + index;
                let src = self.buf.get_ptr(physical_index);
                let dst = self.buf.get_mut_ptr(physical_index + 1);
                unsafe { core::ptr::copy(src, dst, distance_to_back) };
                let ptr = self.buf.get_mut_ptr(physical_index);
                unsafe { ptr.write(value) };
            }
            (false, true, false) => {
                // storage is not contiguous, insertion point is in lower half and does not wrap
                // -> shift all elements before the insertion point to the left by one
                let ptr = self.buf.get_mut_ptr(new_front);
                unsafe {
                    ptr.write(value);
                }
                self.buf.storage_mut()[new_front..].rotate_left(1);
            }
            (false, false, true) => {
                // storage is not contiguous, insertion point is in upper half and does wrap
                // -> shift all elements after the insertion point to the right by one
                let physical_index = (front + index) % self.capacity();
                let ptr = self.buf.get_mut_ptr(physical_index + distance_to_back);
                unsafe {
                    ptr.write(value);
                }
                self.buf.storage_mut()[physical_index..=physical_index + distance_to_back]
                    .rotate_right(1);
            }
            (false, true, true) => {
                // storage is not contiguous, insertion point is in the lower half, but the index wraps
                // -> shift all elements before the insertion point to the left by one, accounting for wrap
                let physical_index = (new_front + index) % self.capacity();
                let ptr = self.buf.get_mut_ptr(0);
                let tmp = unsafe { ptr.replace(value) };
                self.buf.storage_mut()[..=physical_index].rotate_left(1);

                let ptr = self.buf.get_mut_ptr(new_front);
                unsafe {
                    ptr.write(tmp);
                }
                self.buf.storage_mut()[new_front..].rotate_left(1);
            }
            (false, false, false) => {
                // storage is not contiguous, insertion point is in the upper half, but the index doesn't wrap
                // -> shift all elements after the insertion point to the right by one, accounting for wrap
                let physical_index = (front + index) % cap;
                let ptr = self.buf.get_mut_ptr(cap - 1);
                let tmp = unsafe { ptr.replace(value) };
                self.buf.storage_mut()[physical_index..].rotate_right(1);

                let back = back % cap;
                let ptr = self.buf.get_mut_ptr(back);
                unsafe {
                    ptr.write(tmp);
                }
                self.buf.storage_mut()[..back + 1].rotate_right(1);
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
    pub fn insert(&mut self, index: I, value: E) {
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
    pub fn remove(&mut self, index: I) -> Option<E> {
        let index = index.into_usize();
        if index >= self.len() {
            return None;
        }

        let cap = self.capacity();
        let front = self.front.into_usize();
        let back = front + self.len();
        let contiguous = back <= cap;

        let distance_to_front = index;
        let distance_to_back = self.len() - index - 1;
        let move_front = distance_to_front < distance_to_back;

        let index_wrapped = front + index >= cap;
        let physical_index = (front + index) % cap;

        let ptr = self.buf.get_ptr(physical_index);
        let result = unsafe { ptr.read() };

        match (contiguous, move_front, index_wrapped) {
            (true, true, _) | (false, true, false) => {
                // Storage is contiguous, index is in lower half
                // OR Storage is discontiguous, index is in lower half, and does not wrap
                // -> shift all elements before the index to the right
                unsafe {
                    let src = self.buf.storage().as_ptr().add(front);
                    let dst = self.buf.storage_mut().as_mut_ptr().add(front + 1);
                    core::ptr::copy(src, dst, distance_to_front);
                }

                self.front = I::from_usize((front + 1) % cap);
            }
            (true, false, _) | (false, false, true) => {
                // Storage is contiguous, index is in upper half
                // OR Storage is discontiguous, index is in upper half, and does wrap
                // -> shift all elements after the index to the left
                unsafe {
                    let src = self.buf.storage().as_ptr().add(physical_index + 1);
                    let dst = self.buf.storage_mut().as_mut_ptr().add(physical_index);
                    core::ptr::copy(src, dst, distance_to_back);
                }
            }
            (false, true, true) => {
                // Storage is discontiguous, index is in lower half, but also wraps
                // -> shift all elements before the index to the right, accounting for wrap
                unsafe {
                    let src = self.buf.storage().as_ptr();
                    let dst = self.buf.storage_mut().as_mut_ptr().add(1);
                    core::ptr::copy(src, dst, physical_index);

                    let src = self.buf.storage().as_ptr().add(cap - 1);
                    let dst = self.buf.storage_mut().as_mut_ptr();
                    core::ptr::copy(src, dst, 1);

                    let src = self.buf.storage().as_ptr().add(front);
                    let dst = self.buf.storage_mut().as_mut_ptr().add(front + 1);
                    core::ptr::copy(src, dst, cap - front - 1);
                }

                self.front = I::from_usize((front + 1) % cap);
            }
            (false, false, false) => {
                // Storage is discontiguous, index is in upper half, but doesn't wrap
                // -> shift all elements after the index to the left, accounting for wrap
                unsafe {
                    let src = self.buf.storage().as_ptr().add(physical_index + 1);
                    let dst = self.buf.storage_mut().as_mut_ptr().add(physical_index);
                    core::ptr::copy(src, dst, cap - physical_index - 1);

                    let src = self.buf.storage().as_ptr();
                    let dst = self.buf.storage_mut().as_mut_ptr().add(cap - 1);
                    core::ptr::copy(src, dst, 1);

                    let src = self.buf.storage().as_ptr().add(1);
                    let dst = self.buf.storage_mut().as_mut_ptr();
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
    pub fn replace(&mut self, index: I, value: E) -> E {
        let index = self
            .physical_index(index)
            .expect("index out of bounds in `replace`");
        unsafe { self.buf.get_mut_ptr(index).replace(value) }
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
        F: FnMut(&E) -> bool,
    {
        let capacity = self.capacity();
        let old_len = self.len();
        let mut new_len = 0;

        for i in 0..old_len {
            let idx = i % capacity;
            let src = self.buf.get_ptr(idx);
            let retain = f(unsafe { src.as_ref().unwrap() });

            if retain {
                let dst = self.buf.get_mut_ptr(new_len % capacity);
                unsafe { core::ptr::copy(src, dst, 1) };
                new_len += 1;
            } else {
                let to_drop = self.buf.get_mut_ptr(idx);
                unsafe { core::ptr::drop_in_place(to_drop) };
            }
        }

        self.len = I::from_usize(new_len);
    }

    fn rotate_left_inner(&mut self, mid: usize) {
        debug_assert!(mid * 2 <= self.len());

        let cap = self.capacity();
        let front = self.front.into_usize();
        let back = front + self.len();
        let contiguous = back <= cap;

        let first_count = if contiguous {
            // storage is contiguous, use the first copy to (at most) fill the right gap
            usize::min(cap - back, mid)
        } else {
            // storage is discontiguous, use the first copy to (at most) shift over the right section
            usize::min(cap - front, mid)
        };

        let src = self.buf.get_ptr(front);
        let dst = self.buf.get_mut_ptr(back % cap);
        unsafe { core::ptr::copy(src, dst, first_count) };

        let src = self.buf.get_ptr((front + first_count) % cap);
        let dst = self.buf.get_mut_ptr((back + first_count) % cap);
        unsafe { core::ptr::copy(src, dst, mid - first_count) };

        self.front = I::from_usize((front + mid) % cap);
    }

    fn rotate_right_inner(&mut self, k: usize) {
        debug_assert!(k * 2 <= self.len());

        let cap = self.capacity();
        let front = self.front.into_usize();
        let back = front + self.len();
        let contiguous = back <= cap;

        let first_count = if contiguous {
            // storage is contiguous, use the first copy to (at most) fill the left gap
            usize::min(front, k)
        } else {
            // storage is discontiguous, use the first copy to (at most) shift over the left section
            usize::min(back % cap, k)
        };

        let src = self.buf.get_ptr((back - first_count) % cap);
        let dst = self.buf.get_mut_ptr((front + cap - first_count) % cap);
        unsafe { core::ptr::copy(src, dst, first_count) };

        let src = self.buf.get_ptr((back + cap - k) % cap);
        let dst = self.buf.get_mut_ptr((front + cap - k) % cap);
        unsafe { core::ptr::copy(src, dst, k - first_count) };

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
        let mid = mid.into_usize();
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
        let k = k.into_usize();
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
    pub fn as_slices(&self) -> (&[E], &[E]) {
        let front = self.front.into_usize();
        let back = front + self.len();
        if back <= self.capacity() {
            let ptr = self.buf.storage().as_ptr() as *const E;
            let slice = unsafe { core::slice::from_raw_parts(ptr.add(front), self.len()) };
            (slice, &[])
        } else {
            let ptr = self.buf.storage().as_ptr() as *const E;
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
    pub fn as_mut_slices(&mut self) -> (&mut [E], &mut [E]) {
        let front = self.front.into_usize();
        let back = front + self.len();
        if back <= self.capacity() {
            let ptr = self.buf.storage_mut().as_mut_ptr() as *mut E;
            let slice = unsafe { core::slice::from_raw_parts_mut(ptr.add(front), self.len()) };
            (slice, &mut [])
        } else {
            let len = self.len();
            let cap = self.capacity();

            let storage = self.buf.storage_mut();
            let (rest, fst) = storage.split_at_mut(front);
            let (snd, _) = rest.split_at_mut(len - (cap - front));

            let fst = unsafe {
                let ptr = fst.as_mut_ptr() as *mut E;
                core::slice::from_raw_parts_mut(ptr, fst.len())
            };
            let snd = unsafe {
                let ptr = snd.as_mut_ptr() as *mut E;
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
    pub fn make_contiguous(&mut self) -> &mut [E] {
        let front = self.front.into_usize();
        let back = front + self.len();
        if back <= self.capacity() {
            let ptr = self.buf.storage_mut().as_mut_ptr() as *mut E;
            unsafe { core::slice::from_raw_parts_mut(ptr.add(front), self.len()) }
        } else {
            self.buf.storage_mut().rotate_left(front);
            self.front = I::from_usize(0);

            let ptr = self.buf.storage_mut().as_mut_ptr() as *mut E;
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
    pub fn iter(&self) -> Iter<'_, E, B, I> {
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
    pub fn iter_mut(&mut self) -> IterMut<'_, E, B, I> {
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
    pub fn range<R: core::ops::RangeBounds<I>>(&self, range: R) -> Iter<'_, E, B, I> {
        use core::ops::Bound;
        let start = match range.start_bound() {
            Bound::Included(x) => x.into_usize(),
            Bound::Excluded(x) => x.into_usize().saturating_add(1),
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(x) => x.into_usize().saturating_add(1),
            Bound::Excluded(x) => x.into_usize(),
            Bound::Unbounded => self.len(),
        };

        assert!(
            start <= end,
            "Deque::range Illegal range {} to {}",
            start,
            end
        );
        assert!(
            end <= self.len(),
            "Deque::range Range ends at {} but length is only {}",
            end,
            self.len()
        );

        Iter {
            front: I::from_usize((self.front.into_usize() + start) % self.capacity()),
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
    pub fn range_mut<R: core::ops::RangeBounds<I>>(&mut self, range: R) -> IterMut<'_, E, B, I> {
        use core::ops::Bound;
        let start = match range.start_bound() {
            Bound::Included(x) => x.into_usize(),
            Bound::Excluded(x) => x.into_usize().saturating_add(1),
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(x) => x.into_usize().saturating_add(1),
            Bound::Excluded(x) => x.into_usize(),
            Bound::Unbounded => self.len(),
        };

        assert!(
            start <= end,
            "Deque::range_mut Illegal range {} to {}",
            start,
            end
        );
        assert!(
            end <= self.len(),
            "Deque::range_mut Range ends at {} but length is only {}",
            end,
            self.len()
        );

        IterMut {
            front: I::from_usize((self.front.into_usize() + start) % self.capacity()),
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
    pub fn drain<R: core::ops::RangeBounds<I>>(&mut self, range: R) -> Drain<'_, E, B, I> {
        use core::ops::Bound;
        let start = match range.start_bound() {
            Bound::Included(x) => x.into_usize(),
            Bound::Excluded(x) => x.into_usize().saturating_add(1),
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(x) => x.into_usize().saturating_add(1),
            Bound::Excluded(x) => x.into_usize(),
            Bound::Unbounded => self.len(),
        };

        assert!(
            start <= end,
            "Deque::drain Illegal range {} to {}",
            start,
            end
        );
        assert!(
            end <= self.len(),
            "Deque::drain Range ends at {} but length is only {}",
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

impl<E, B, I> core::ops::Index<I> for Deque<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    type Output = E;

    #[inline]
    fn index(&self, index: I) -> &E {
        self.get(index).expect("out of bounds access")
    }
}

impl<E, B, I> core::ops::IndexMut<I> for Deque<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut E {
        self.get_mut(index).expect("out of bounds access")
    }
}

impl<E, B, I> Drop for Deque<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
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

impl<E, B, I> core::fmt::Debug for Deque<E, B, I>
where
    E: core::fmt::Debug,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let (front, back) = self.as_slices();
        f.debug_list().entries(front).entries(back).finish()
    }
}

impl<E, B, I> core::hash::Hash for Deque<E, B, I>
where
    E: core::hash::Hash,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        let (front, back) = self.as_slices();
        core::hash::Hash::hash_slice(front, state);
        core::hash::Hash::hash_slice(back, state);
    }
}

impl<AE, AB, AI, BE, BB, BI> PartialEq<Deque<BE, BB, BI>> for Deque<AE, AB, AI>
where
    AE: PartialEq<BE>,
    AB: ContiguousStorage<AE>,
    BB: ContiguousStorage<BE>,
    AI: Capacity,
    BI: Capacity,
{
    fn eq(&self, other: &Deque<BE, BB, BI>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        let (self_front, self_back) = self.as_slices();
        let (other_front, other_back) = other.as_slices();
        if self_front.len() == other_front.len() {
            self_front == other_front && self_back == other_back
        } else if self_front.len() < other_front.len() {
            let a = self_front.len();
            let b = other_front.len() - a;
            debug_assert_eq!(self_back[..b].len(), other_front[a..].len());
            debug_assert_eq!(self_back[b..].len(), other_back.len());
            self_front == &other_front[..a]
                && &self_back[..b] == &other_front[a..]
                && &self_back[b..] == other_back
        } else {
            let a = other_front.len();
            let b = self_front.len() - a;
            debug_assert_eq!(self_front[a..].len(), other_back[..b].len());
            debug_assert_eq!(self_back.len(), other_back[b..].len());
            &self_front[..a] == other_front
                && &self_front[a..] == &other_back[..b]
                && self_back == &other_back[b..]
        }
    }
}

impl<E, B, I> Eq for Deque<E, B, I>
where
    E: Eq,
    B: ContiguousStorage<E>,
    I: Capacity,
{
}

impl<E, B, I, R> PartialEq<R> for Deque<E, B, I>
where
    E: PartialEq,
    B: ContiguousStorage<E>,
    I: Capacity,
    R: AsRef<[E]>,
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

impl<E, AB, AI, BB, BI> PartialOrd<Deque<E, BB, BI>> for Deque<E, AB, AI>
where
    E: PartialOrd,
    AB: ContiguousStorage<E>,
    BB: ContiguousStorage<E>,
    AI: Capacity,
    BI: Capacity,
{
    fn partial_cmp(&self, other: &Deque<E, BB, BI>) -> Option<core::cmp::Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<E, B, I> Ord for Deque<E, B, I>
where
    E: Ord,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<E, B, I> core::iter::Extend<E> for Deque<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn extend<T: IntoIterator<Item = E>>(&mut self, iter: T) {
        iter.into_iter().for_each(|item| self.push_back(item));
    }
}

impl<'a, E, B, I> core::iter::Extend<&'a E> for Deque<E, B, I>
where
    E: 'a + Clone,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn extend<T: IntoIterator<Item = &'a E>>(&mut self, iter: T) {
        iter.into_iter()
            .for_each(|item| self.push_back(item.clone()));
    }
}

/// An iterator over the elements of a deque.
///
/// This `struct` is created by the [`iter`](Deque::iter) method on [`Deque`].
/// See its documentation for more.
pub struct Iter<'a, E, B, I>
where
    E: 'a,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    front: I,
    len: I,
    buf: &'a B,
    _ref: PhantomData<&'a E>,
}

impl<'a, E, B, I> core::fmt::Debug for Iter<'a, E, B, I>
where
    E: 'a + core::fmt::Debug,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let (front, back) = {
            let front = self.front.into_usize();
            let back = front + self.len.into_usize();

            if back <= self.buf.capacity() {
                unsafe {
                    (
                        core::slice::from_raw_parts(self.buf.get_ptr(front), self.len.into_usize()),
                        &[][..],
                    )
                }
            } else {
                unsafe {
                    (
                        core::slice::from_raw_parts(
                            self.buf.get_ptr(front),
                            self.buf.capacity() - front,
                        ),
                        core::slice::from_raw_parts(
                            self.buf.get_ptr(0),
                            back - self.buf.capacity(),
                        ),
                    )
                }
            }
        };

        f.debug_tuple("Iter").field(&front).field(&back).finish()
    }
}

impl<'a, E, B, I> Iterator for Iter<'a, E, B, I>
where
    E: 'a,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    type Item = &'a E;

    #[inline]
    fn next(&mut self) -> Option<&'a E> {
        let len = self.len.into_usize();
        if len == 0 {
            return None;
        }

        let front = self.front.into_usize();
        self.front = I::from_usize((front + 1) % self.buf.capacity());
        self.len = I::from_usize(len - 1);
        let result = unsafe { self.buf.get_ptr(front).as_ref() };
        debug_assert!(result.is_some());
        result
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len.into_usize();
        (len, Some(len))
    }
}

impl<'a, E, B, I> DoubleEndedIterator for Iter<'a, E, B, I>
where
    E: 'a,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    #[inline]
    fn next_back(&mut self) -> Option<&'a E> {
        let len = self.len.into_usize();
        if len == 0 {
            return None;
        }

        let front = self.front.into_usize();
        let idx = (front + len - 1) % self.buf.capacity();
        self.len = I::from_usize(len - 1);
        let result = unsafe { self.buf.get_ptr(idx).as_ref() };
        debug_assert!(result.is_some());
        result
    }
}

impl<E, B: ContiguousStorage<E>, I: Capacity> ExactSizeIterator for Iter<'_, E, B, I> {}
impl<E, B: ContiguousStorage<E>, I: Capacity> core::iter::FusedIterator for Iter<'_, E, B, I> {}

/// A mutable iterator over the elements of a deque.
///
/// This `struct` is created by the [`iter_mut`](Deque::iter_mut) method on [`Deque`].
/// See its documentation for more.
pub struct IterMut<'a, E, B, I>
where
    E: 'a,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    front: I,
    len: I,
    buf: &'a mut B,
    _ref: PhantomData<&'a mut E>,
}

impl<'a, E, B, I> core::fmt::Debug for IterMut<'a, E, B, I>
where
    E: 'a + core::fmt::Debug,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let (front, back) = {
            let front = self.front.into_usize();
            let back = front + self.len.into_usize();

            if back <= self.buf.capacity() {
                unsafe {
                    (
                        core::slice::from_raw_parts(self.buf.get_ptr(front), self.len.into_usize()),
                        &[][..],
                    )
                }
            } else {
                unsafe {
                    (
                        core::slice::from_raw_parts(
                            self.buf.get_ptr(front),
                            self.buf.capacity() - front,
                        ),
                        core::slice::from_raw_parts(
                            self.buf.get_ptr(0),
                            back - self.buf.capacity(),
                        ),
                    )
                }
            }
        };

        f.debug_tuple("Iter").field(&front).field(&back).finish()
    }
}

impl<'a, E, B, I> Iterator for IterMut<'a, E, B, I>
where
    E: 'a,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    type Item = &'a mut E;

    #[inline]
    fn next(&mut self) -> Option<&'a mut E> {
        let len = self.len.into_usize();
        if len == 0 {
            return None;
        }

        let front = self.front.into_usize();
        self.front = I::from_usize((front + 1) % self.buf.capacity());
        self.len = I::from_usize(len - 1);
        let result = unsafe { self.buf.get_mut_ptr(front).as_mut() };
        debug_assert!(result.is_some());
        result
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len.into_usize();
        (len, Some(len))
    }
}

impl<'a, E, B, I> DoubleEndedIterator for IterMut<'a, E, B, I>
where
    E: 'a,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut E> {
        let len = self.len.into_usize();
        if len == 0 {
            return None;
        }

        let front = self.front.into_usize();
        let idx = (front + len - 1) % self.buf.capacity();
        self.len = I::from_usize(len - 1);
        let result = unsafe { self.buf.get_mut_ptr(idx).as_mut() };
        debug_assert!(result.is_some());
        result
    }
}

impl<E, B: ContiguousStorage<E>, I: Capacity> ExactSizeIterator for IterMut<'_, E, B, I> {}
impl<E, B: ContiguousStorage<E>, I: Capacity> core::iter::FusedIterator for IterMut<'_, E, B, I> {}

/// An owning iterator over the elements of a deque.
///
/// This `struct` is created by the [`into_iter`](Deque::into_iter) method on
/// [`Deque`] (provided by the `IntoIterator` trait). See its documentation for
/// more.
pub struct IntoIter<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    inner: Deque<E, B, I>,
}

impl<E, B, I> core::fmt::Debug for IntoIter<E, B, I>
where
    E: core::fmt::Debug,
    B: ContiguousStorage<E>,
    I: Capacity,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("IntoIterator").field(&self.inner).finish()
    }
}

impl<E, B, I> Iterator for IntoIter<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    type Item = E;

    #[inline]
    fn next(&mut self) -> Option<E> {
        self.inner.pop_front()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.inner.len();
        (len, Some(len))
    }
}

impl<E, B, I> DoubleEndedIterator for IntoIter<E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    #[inline]
    fn next_back(&mut self) -> Option<E> {
        self.inner.pop_back()
    }
}

impl<E, B: ContiguousStorage<E>, I: Capacity> ExactSizeIterator for IntoIter<E, B, I> {}
impl<E, B: ContiguousStorage<E>, I: Capacity> core::iter::FusedIterator for IntoIter<E, B, I> {}

impl<E, B: ContiguousStorage<E>, I: Capacity> IntoIterator for Deque<E, B, I> {
    type Item = E;
    type IntoIter = IntoIter<E, B, I>;

    /// Converts the `Deque` into a front-to-back iterator yielding elements by value.
    fn into_iter(self) -> IntoIter<E, B, I> {
        IntoIter { inner: self }
    }
}

impl<'a, E, B: ContiguousStorage<E>, I: Capacity> IntoIterator for &'a Deque<E, B, I> {
    type Item = &'a E;
    type IntoIter = Iter<'a, E, B, I>;

    fn into_iter(self) -> Iter<'a, E, B, I> {
        self.iter()
    }
}

impl<'a, E, B: ContiguousStorage<E>, I: Capacity> IntoIterator for &'a mut Deque<E, B, I> {
    type Item = &'a mut E;
    type IntoIter = IterMut<'a, E, B, I>;

    fn into_iter(self) -> IterMut<'a, E, B, I> {
        self.iter_mut()
    }
}

/// A draining iterator over the elements of a deque.
///
/// This `struct` is created by the [`drain`](Deque::drain) method on [`Deque`].
/// See its documentation for more.
pub struct Drain<'p, E, B, I>
where
    B: ContiguousStorage<E>,
    I: Capacity,
{
    parent: &'p mut Deque<E, B, I>,
    target_start: usize,
    front_index: usize,
    back_index: usize,
    target_end: usize,
}

impl<E, B: ContiguousStorage<E>, I: Capacity> core::fmt::Debug for Drain<'_, E, B, I>
where
    E: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
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

impl<E, B: ContiguousStorage<E>, I: Capacity> Iterator for Drain<'_, E, B, I> {
    type Item = E;

    #[inline]
    fn next(&mut self) -> Option<E> {
        if self.front_index == self.back_index {
            return None;
        }

        let idx = (self.parent.front.into_usize() + self.front_index) % self.parent.capacity();
        self.front_index += 1;

        unsafe { Some(self.parent.buf.get_ptr(idx).read()) }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.back_index - self.front_index;
        (len, Some(len))
    }
}

impl<E, B: ContiguousStorage<E>, I: Capacity> DoubleEndedIterator for Drain<'_, E, B, I> {
    #[inline]
    fn next_back(&mut self) -> Option<E> {
        if self.back_index == self.front_index {
            return None;
        }

        let idx = (self.parent.front.into_usize() + self.back_index - 1) % self.parent.capacity();
        self.back_index -= 1;

        unsafe { Some(self.parent.buf.get_ptr(idx).read()) }
    }
}

impl<E, B: ContiguousStorage<E>, I: Capacity> ExactSizeIterator for Drain<'_, E, B, I> {}
impl<E, B: ContiguousStorage<E>, I: Capacity> core::iter::FusedIterator for Drain<'_, E, B, I> {}

impl<E, B: ContiguousStorage<E>, I: Capacity> Drop for Drain<'_, E, B, I> {
    fn drop(&mut self) {
        // 1. drop any items that remain untaken
        let cap = self.parent.capacity();
        let front = self.parent.front.into_usize() + self.front_index;
        let back = self.parent.front.into_usize() + self.back_index;
        debug_assert!(back >= front);

        if front >= cap || back <= cap {
            // remaining items are contiguous, drop as single slice
            let ptr = self.parent.buf.get_mut_ptr(front % cap);
            unsafe { core::ptr::slice_from_raw_parts_mut(ptr, back - front).drop_in_place() };
        } else {
            // remaining items are discontiguous, account for wrapping
            let ptr = self.parent.buf.get_mut_ptr(front);
            let len = cap - front;
            unsafe { core::ptr::slice_from_raw_parts_mut(ptr, len).drop_in_place() };

            let ptr = self.parent.buf.get_mut_ptr(0);
            let len = (back - front) - len;
            unsafe { core::ptr::slice_from_raw_parts_mut(ptr, len).drop_in_place() };
        }

        // 2. choose which portion of the unaffected items to shift over to close the gap
        let front = self.parent.front.into_usize();
        let back = front + self.parent.len();
        let target_start = front + self.target_start;
        let target_end = front + self.target_end;
        let target_wrapped = target_start <= cap && cap <= target_end;

        let distance_to_front = self.target_start;
        let distance_to_back = self.parent.len() - self.target_end;
        let move_front = distance_to_front < distance_to_back;
        let source_wrapped = if move_front {
            front < cap && cap < target_start
        } else {
            target_end < cap && cap < back
        };

        match (move_front, target_wrapped, source_wrapped) {
            (false, false, false) => {
                // wrap point is outside relevant range, move back in one copy
                let src = self.parent.buf.get_ptr(target_end % cap);
                let dst = self.parent.buf.get_mut_ptr(target_start % cap);
                unsafe { core::ptr::copy(src, dst, distance_to_back) };
            }
            (true, false, false) => {
                // wrap point is outside relevant range, move front in one copy
                let new_front = target_end - distance_to_front;
                self.parent.front = I::from_usize(new_front);

                let src = self.parent.buf.get_ptr(front);
                let dst = self.parent.buf.get_mut_ptr(new_front);
                unsafe { core::ptr::copy(src, dst, distance_to_front) };
            }
            (false, true, false) => {
                // wrap point is inside target range, move back in two copies
                let fst_count = usize::min(cap - target_start, distance_to_back);
                let src = self.parent.buf.get_ptr(target_end % cap);
                let dst = self.parent.buf.get_mut_ptr(target_start % cap);
                unsafe { core::ptr::copy(src, dst, fst_count) };

                let src = self.parent.buf.get_ptr((target_end + fst_count) % cap);
                let dst = self
                    .parent
                    .buf
                    .get_mut_ptr((target_start + fst_count) % cap);
                unsafe { core::ptr::copy(src, dst, distance_to_back - fst_count) };
            }
            (true, true, false) => {
                // wrap point is inside target range, move front in two copies
                let fst_count = usize::min(target_end - cap, distance_to_front);
                let src = self.parent.buf.get_ptr(target_start - fst_count);
                let dst = self.parent.buf.get_mut_ptr((target_end - fst_count) % cap);
                unsafe { core::ptr::copy(src, dst, fst_count) };

                let new_front = (target_end - distance_to_front) % cap;
                self.parent.front = I::from_usize(new_front);

                let src = self.parent.buf.get_ptr(front);
                let dst = self.parent.buf.get_mut_ptr(new_front);
                unsafe { core::ptr::copy(src, dst, distance_to_front - fst_count) };
            }
            (false, false, true) => {
                // wrap point is inside source range, move back in three copies
                let fst_count = cap - target_end;
                let src = self.parent.buf.get_ptr(target_end);
                let dst = self.parent.buf.get_mut_ptr(target_start);
                unsafe { core::ptr::copy(src, dst, fst_count) };

                let remaining = distance_to_back - fst_count;
                let snd_count = usize::min(cap - (target_start + fst_count), remaining);
                let src = self.parent.buf.get_ptr(0);
                let dst = self.parent.buf.get_mut_ptr(target_start + fst_count);
                unsafe { core::ptr::copy(src, dst, snd_count) };

                let remaining = remaining - snd_count;
                let src = self.parent.buf.get_ptr(snd_count);
                let dst = self.parent.buf.get_mut_ptr(0);
                unsafe { core::ptr::copy(src, dst, remaining) };
            }
            (true, false, true) => {
                // wrap point is inside source range, move front in three copies
                let fst_count = target_start - cap;
                let src = self.parent.buf.get_ptr(0);
                let dst = self.parent.buf.get_mut_ptr(target_end - cap - fst_count);
                unsafe { core::ptr::copy(src, dst, fst_count) };

                let remaining = distance_to_front - fst_count;
                let snd_count = usize::min(target_end - cap - fst_count, remaining);
                let src = self.parent.buf.get_ptr(cap - snd_count);
                let dst = self
                    .parent
                    .buf
                    .get_mut_ptr(target_end - cap - (fst_count + snd_count));
                unsafe { core::ptr::copy(src, dst, snd_count) };

                let new_front = (front + (target_end - target_start)) % cap;
                self.parent.front = I::from_usize(new_front);

                let remaining = remaining - snd_count;
                let src = self.parent.buf.get_ptr(front);
                let dst = self.parent.buf.get_mut_ptr(new_front);
                unsafe { core::ptr::copy(src, dst, remaining) };
            }
            (_, true, true) => {
                // wrap point cannot be in both the source and target ranges!
                unreachable!();
            }
        }

        let new_len = self.parent.len() - (target_end - target_start);
        self.parent.len = I::from_usize(new_len);
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
pub type AllocDeque<E, I = usize> = Deque<E, crate::storage::HeapStorage<E>, I>;

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<E: Copy, I: Capacity> AllocDeque<E, I> {
    /// Creates an empty `AllocDeque` with the specified capacity.
    ///
    /// # Panics
    /// Panics if `capacity` cannot be represented by a `usize`.
    pub fn with_capacity(capacity: I) -> Self {
        Deque {
            front: I::from_usize(0),
            len: I::from_usize(0),
            buf: alloc::vec![core::mem::MaybeUninit::uninit(); capacity.into_usize()]
                .into_boxed_slice(),
            elem: PhantomData,
        }
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<E: Copy, I: Capacity> Clone for AllocDeque<E, I> {
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
/// let mut deque = coca::ArrayDeque::<char, 4>::new();
/// deque.push_front('b');
/// deque.push_front('a');
/// deque.push_back('c');
/// deque.push_back('d');
/// assert_eq!(deque, &['a', 'b', 'c', 'd']);
/// assert_eq!(deque.try_push_back('e'), Err('e'));
/// ```
#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
pub type ArrayDeque<E, const C: usize> = Deque<E, crate::storage::InlineStorage<E, C>, usize>;

/// A deque using an inline array for storage, generic over the index type.
///
/// # Examples
/// ```
/// let mut deque = coca::TiArrayDeque::<char, u8, 4>::new();
/// deque.push_front('a');
/// assert_eq!(deque[0u8], 'a');
/// ```
#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
pub type TiArrayDeque<E, I, const C: usize> = Deque<E, crate::storage::InlineStorage<E, C>, I>;

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
impl<E, I: Capacity, const C: usize> Deque<E, [core::mem::MaybeUninit<E>; C], I> {
    /// Constructs a new deque backed by an inline array.
    ///
    /// # Panics
    /// Panics if `C` cannot be represented as a value of type `I`.
    ///
    /// # Examples
    /// ```
    /// let deque = coca::ArrayDeque::<u32, 7>::new();
    /// assert_eq!(deque.len(), 0);
    /// assert_eq!(deque.capacity(), 7);
    /// ```
    #[inline]
    pub fn new() -> Self {
        I::from_usize(C);

        Deque {
            front: I::from_usize(0),
            len: I::from_usize(0),
            buf: unsafe { core::mem::MaybeUninit::uninit().assume_init() },
            elem: PhantomData,
        }
    }
}

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
impl<E, I: Capacity, const C: usize> Default for Deque<E, [core::mem::MaybeUninit<E>; C], I> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
impl<E: Clone, I: Capacity, const C: usize> Clone for Deque<E, [core::mem::MaybeUninit<E>; C], I> {
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
