//! A double-ended queue implemented with a ring buffer.
//!
//! This queue has O(1) inserts and removals from both ends of the sequence.
//! It also has O(1) indexing like a vector.

use core::marker::PhantomData;

use crate::storage::{Capacity, ContiguousStorage};

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
pub struct Deque<E, B, I> {
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
        unsafe { Some(self.buf.storage()[index].as_ptr().as_ref().unwrap()) }
    }

    /// Returns a mutable reference to the element at the given index, or [`None`]
    /// if the index is out of bounds.
    ///
    /// The element at index 0 is the front of the queue.
    #[inline]
    pub fn get_mut(&mut self, index: I) -> Option<&mut E> {
        let index = self.physical_index(index)?;
        unsafe { Some(self.buf.storage_mut()[index].as_mut_ptr().as_mut().unwrap()) }
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
        let result = unsafe { self.buf.storage()[front].as_ptr().read() };
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
        let result = unsafe { self.buf.storage()[idx].as_ptr().read() };
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
        let ptr = self.buf.storage_mut()[idx].as_mut_ptr();
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
        let ptr = self.buf.storage_mut()[end].as_mut_ptr();
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
    /// assert_eq!(deque.make_contiguous(), &[1, 2, 3]);
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
    /// assert_eq!(deque.make_contiguous(), &[2, 1]);
    /// ```
    pub fn swap_remove_front(&mut self, index: I) -> Option<E> {
        let index = self.physical_index(index)?;
        let front = self.front.into_usize();

        unsafe {
            let last = self.buf.storage()[front].as_ptr().read();
            let hole = self.buf.storage_mut()[index].as_mut_ptr();
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
    /// assert_eq!(deque.make_contiguous(), &[3, 2]);
    /// ```
    pub fn swap_remove_back(&mut self, index: I) -> Option<E> {
        let index = self.physical_index(index)?;
        let back = (self.front.into_usize() + self.len() - 1) % self.capacity();

        unsafe {
            let last = self.buf.storage()[back].as_ptr().read();
            let hole = self.buf.storage_mut()[index].as_mut_ptr();
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
    /// assert_eq!(deque.make_contiguous(), &['a', 'b', 'c'][..]);
    ///
    /// assert!(deque.try_insert(1, 'd').is_ok());
    /// assert_eq!(deque.make_contiguous(), &['a', 'd', 'b', 'c'][..]);
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
                    let dst = self.buf.storage_mut()[new_front].as_mut_ptr();
                    let src = self.buf.storage()[front].as_ptr();
                    unsafe { core::ptr::copy(src, dst, 1) };

                    let dst = self.buf.storage_mut()[front].as_mut_ptr();
                    let src = self.buf.storage()[front + 1].as_ptr();
                    unsafe { core::ptr::copy(src, dst, distance_to_front - 1) };
                }

                let ptr = self.buf.storage_mut()[(new_front + index) % cap].as_mut_ptr();
                unsafe { ptr.write(value) };
            }
            (true, false, _) => {
                // storage is contiguous, insertion point is in upper half
                // -> shift all elements after the insertion point to the right by one
                let physical_index = front + index;
                let src = self.buf.storage()[physical_index].as_ptr();
                let dst = self.buf.storage_mut()[physical_index + 1].as_mut_ptr();
                unsafe { core::ptr::copy(src, dst, distance_to_back) };
                let ptr = self.buf.storage_mut()[physical_index].as_mut_ptr();
                unsafe { ptr.write(value) };
            }
            (false, true, false) => {
                // storage is not contiguous, insertion point is in lower half and does not wrap
                // -> shift all elements before the insertion point to the left by one
                let ptr = self.buf.storage_mut()[new_front].as_mut_ptr();
                unsafe {
                    ptr.write(value);
                }
                self.buf.storage_mut()[new_front..].rotate_left(1);
            }
            (false, false, true) => {
                // storage is not contiguous, insertion point is in upper half and does wrap
                // -> shift all elements after the insertion point to the right by one
                let physical_index = (front + index) % self.capacity();
                let ptr = self.buf.storage_mut()[physical_index + distance_to_back].as_mut_ptr();
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
                let ptr = self.buf.storage_mut()[0].as_mut_ptr();
                let tmp = unsafe { ptr.replace(value) };
                self.buf.storage_mut()[..=physical_index].rotate_left(1);

                let ptr = self.buf.storage_mut()[new_front].as_mut_ptr();
                unsafe {
                    ptr.write(tmp);
                }
                self.buf.storage_mut()[new_front..].rotate_left(1);
            }
            (false, false, false) => {
                // storage is not contiguous, insertion point is in the upper half, but the index doesn't wrap
                // -> shift all elements after the insertion point to the right by one, accounting for wrap
                let physical_index = (front + index) % cap;
                let ptr = self.buf.storage_mut()[cap - 1].as_mut_ptr();
                let tmp = unsafe { ptr.replace(value) };
                self.buf.storage_mut()[physical_index..].rotate_right(1);

                let back = back % cap;
                let ptr = self.buf.storage_mut()[back].as_mut_ptr();
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
    /// assert_eq!(deque.make_contiguous(), &[1, 3][..]);
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

        let ptr = self.buf.storage()[physical_index].as_ptr();
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
    /// assert_eq!(deque.make_contiguous(), &[1, 2, 3][..]);
    /// ```
    pub fn replace(&mut self, index: I, value: E) -> E {
        let index = self
            .physical_index(index)
            .expect("index out of bounds in `replace`");
        unsafe { self.buf.storage_mut()[index].as_mut_ptr().replace(value) }
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
            let ptr = self.buf.storage_mut().as_mut_ptr() as *mut E;
            let fst =
                unsafe { core::slice::from_raw_parts_mut(ptr.add(front), self.capacity() - front) };
            let snd = unsafe {
                core::slice::from_raw_parts_mut(ptr, self.len() - (self.capacity() - front))
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
    /// assert_eq!(deque.make_contiguous(), &[2, 1]);
    ///
    /// deque.push_front(3);
    /// assert_eq!(deque.make_contiguous(), &[3, 2, 1]);
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
}
