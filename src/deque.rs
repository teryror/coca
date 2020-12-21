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
