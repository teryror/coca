//! Densely packed object pools with indirect indexing using stable handles.
//!
//! Values are packed into a contiguously populated array, which optimizes for
//! iteration speed. For random accesses, the physical array position has to be
//! looked up in a separate, incontiguously populated table.

use core::alloc::{Layout, LayoutError};
use core::fmt::{Debug, Formatter};
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ops::{Index, IndexMut};

use super::{buffer_too_large_for_handle_type, DebugEntry, DefaultHandle, Handle};
use crate::storage::{Capacity, LayoutSpec, Storage};

/// The [`LayoutSpec`] for a [`PackedPool`].
pub struct PackedPoolLayout<T, H>(PhantomData<(T, H)>);
impl<T, H: Handle> LayoutSpec for PackedPoolLayout<T, H> {
    type Item = (T, H, u32, H::Index);

    fn layout_with_capacity(items: usize) -> Result<Layout, LayoutError> {
        let values_array = Layout::array::<T>(items)?;
        let handles_array = Layout::array::<H>(items)?;
        let counters_array = Layout::array::<u32>(items)?;
        let index_array = Layout::array::<H::Index>(items)?;

        let (extended, _) = values_array.extend(handles_array)?;
        let (extended, _) = extended.extend(counters_array)?;
        let (extended, _) = extended.extend(index_array)?;

        Ok(extended.pad_to_align())
    }
}

/// A densely packed object pool with constant capacity.
///
/// See the [super module documentation](crate::collections::pool) for information on
/// pool-based memory management, and [this module's documentation](crate::collections::pool::packed)
/// for details on this variation of it.
pub struct PackedPool<T, S: Storage<PackedPoolLayout<T, H>>, H: Handle = DefaultHandle> {
    buf: S,
    len: H::Index,
    next_free_slot: H::Index,
    items: PhantomData<T>,
}

impl<T, S: Storage<PackedPoolLayout<T, H>>, H: Handle> From<S> for PackedPool<T, S, H> {
    fn from(buf: S) -> Self {
        let cap = buf.capacity();
        if cap >= H::MAX_INDEX {
            buffer_too_large_for_handle_type::<H>();
        }

        let mut result = PackedPool {
            buf,
            len: H::Index::from_usize(0),
            next_free_slot: H::Index::from_usize(0),
            items: PhantomData,
        };

        // initialize free list:
        let mut ptr = result.next_free_slot_or_packed_index_array_mut();
        for i in 1..cap {
            unsafe {
                *ptr = H::Index::from_usize(i);
                ptr = ptr.add(1);
            }
        }

        let sentinel = H::Index::from_usize(Self::FREE_LIST_SENTINEL);
        unsafe {
            *ptr = sentinel;
        }

        // initialize generation counters:
        unsafe {
            core::ptr::write_bytes(result.counters_mut(), 0x00, cap);
        }

        result
    }
}

impl<T, S: Storage<PackedPoolLayout<T, H>>, H: Handle> PackedPool<T, S, H> {
    const FREE_LIST_SENTINEL: usize = H::Index::MAX_REPRESENTABLE;

    #[inline]
    fn values_ptr(&self) -> *const T {
        self.buf.get_ptr().cast()
    }

    #[inline]
    fn values_mut_ptr(&mut self) -> *mut T {
        self.buf.get_mut_ptr().cast()
    }

    #[inline]
    fn handles_ptr(&self) -> *const H {
        let cap = self.buf.capacity();
        let values_array = Layout::array::<T>(cap).unwrap();
        let handles_array = Layout::array::<H>(cap).unwrap();
        let (_, offset) = values_array.extend(handles_array).unwrap();

        let base_ptr = self.buf.get_ptr();
        unsafe { base_ptr.add(offset) }.cast()
    }

    #[inline]
    fn handles_mut_ptr(&mut self) -> *mut H {
        let cap = self.buf.capacity();
        let values_array = Layout::array::<T>(cap).unwrap();
        let handles_array = Layout::array::<H>(cap).unwrap();
        let (_, offset) = values_array.extend(handles_array).unwrap();

        let base_ptr = self.buf.get_mut_ptr();
        unsafe { base_ptr.add(offset) }.cast()
    }

    #[inline]
    fn counters(&self) -> *const u32 {
        let cap = self.buf.capacity();
        let values_array = Layout::array::<T>(cap).unwrap();
        let handles_array = Layout::array::<H>(cap).unwrap();
        let counters_array = Layout::array::<u32>(cap).unwrap();

        let (extended, _) = values_array.extend(handles_array).unwrap();
        let (_, offset) = extended.extend(counters_array).unwrap();

        let base_ptr = self.buf.get_ptr();
        unsafe { base_ptr.add(offset) }.cast()
    }

    #[inline]
    fn counters_mut(&mut self) -> *mut u32 {
        let cap = self.buf.capacity();
        let values_array = Layout::array::<T>(cap).unwrap();
        let handles_array = Layout::array::<H>(cap).unwrap();
        let counters_array = Layout::array::<u32>(cap).unwrap();

        let (extended, _) = values_array.extend(handles_array).unwrap();
        let (_, offset) = extended.extend(counters_array).unwrap();

        let base_ptr = self.buf.get_mut_ptr();
        unsafe { base_ptr.add(offset) }.cast()
    }

    #[inline]
    fn next_free_slot_or_packed_index_array(&self) -> *const H::Index {
        let cap = self.buf.capacity();
        let values_array = Layout::array::<T>(cap).unwrap();
        let handles_array = Layout::array::<H>(cap).unwrap();
        let counters_array = Layout::array::<u32>(cap).unwrap();
        let nfsopi_array = Layout::array::<H::Index>(cap).unwrap();

        let (extended, _) = values_array.extend(handles_array).unwrap();
        let (extended, _) = extended.extend(counters_array).unwrap();
        let (_, offset) = extended.extend(nfsopi_array).unwrap();

        let base_ptr = self.buf.get_ptr();
        unsafe { base_ptr.add(offset) }.cast()
    }

    #[inline]
    fn next_free_slot_or_packed_index_array_mut(&mut self) -> *mut H::Index {
        let cap = self.buf.capacity();
        let values_array = Layout::array::<T>(cap).unwrap();
        let handles_array = Layout::array::<H>(cap).unwrap();
        let counters_array = Layout::array::<u32>(cap).unwrap();
        let nfsopi_array = Layout::array::<H::Index>(cap).unwrap();

        let (extended, _) = values_array.extend(handles_array).unwrap();
        let (extended, _) = extended.extend(counters_array).unwrap();
        let (_, offset) = extended.extend(nfsopi_array).unwrap();

        let base_ptr = self.buf.get_mut_ptr();
        unsafe { base_ptr.add(offset) }.cast()
    }

    /// Returns the number of elements the pool can hold.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Returns the number of elements currently in the pool.
    #[inline]
    pub fn len(&self) -> usize {
        self.len.as_usize()
    }

    /// Returns [`true`] if the pool contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns [`true`] if the pool contains the maximum number of elements.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len() == self.capacity()
    }

    /// Returns a slice of all values currently held in the pool in arbitrary order.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::PackedInlinePool;
    /// let mut pool = PackedInlinePool::<u128, 16>::new();
    /// let h0 = pool.insert(0);
    /// let h1 = pool.insert(1);
    /// let h2 = pool.insert(2);
    ///
    /// let values = pool.values();
    /// assert_eq!(values.len(), 3);
    /// assert!(values.contains(&0));
    /// assert!(values.contains(&1));
    /// assert!(values.contains(&2));
    /// ```
    #[inline]
    pub fn values(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.values_ptr(), self.len()) }
    }

    /// Returns a mutable slice of all values currently held in the pool in an arbitrary order.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::PackedInlinePool;
    /// let mut pool = PackedInlinePool::<u128, 16>::new();
    /// let h0 = pool.insert(0);
    /// let h1 = pool.insert(1);
    /// let h2 = pool.insert(2);
    ///
    /// for v in pool.values_mut() {
    ///     *v *= 10;
    /// }
    ///
    /// assert_eq!(pool.get(h0), Some(&0));
    /// assert_eq!(pool.get(h1), Some(&10));
    /// assert_eq!(pool.get(h2), Some(&20));
    /// ```
    #[inline]
    pub fn values_mut(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.values_mut_ptr(), self.len()) }
    }

    /// Returns a slice of all handles currently valid for the pool in an arbitrary order.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::PackedInlinePool;
    /// let mut pool = PackedInlinePool::<u128, 16>::new();
    /// let h0 = pool.insert(0);
    /// let h1 = pool.insert(1);
    /// let h2 = pool.insert(2);
    ///
    /// let handles = pool.handles();
    /// assert_eq!(handles.len(), 3);
    /// assert!(handles.contains(&h0));
    /// assert!(handles.contains(&h1));
    /// assert!(handles.contains(&h2));
    /// ```
    #[inline]
    pub fn handles(&self) -> &[H] {
        unsafe { core::slice::from_raw_parts(self.handles_ptr(), self.len()) }
    }

    /// Returns a slice of all handles currently valid for the pool, and a
    /// mutable slice of all values it currently holds, in matching arbitrary
    /// order.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::PackedInlinePool;
    /// let mut pool = PackedInlinePool::<u128, 16>::new();
    /// let h0 = pool.insert(0);
    /// let h1 = pool.insert(1);
    ///
    /// let (handles, values) = pool.handles_and_values_mut();
    /// assert_eq!(handles.len(), 2);
    /// assert_eq!(values.len(), 2);
    ///
    /// let handles_copy = [handles[0], handles[1]];
    /// for v in values {
    ///     *v *= 10;
    /// }
    ///
    /// for &h in &handles_copy {
    ///     if h == h0 { assert_eq!(pool.get(h), Some(&0)); }
    ///     else if h == h1 { assert_eq!(pool.get(h), Some(&10)); }
    ///     else { unreachable!(); }
    /// }
    /// ```
    #[inline]
    pub fn handles_and_values_mut(&mut self) -> (&[H], &mut [T]) {
        let len = self.len();
        let handles_ptr = self.handles_ptr();
        let values_ptr = self.values_mut_ptr();

        unsafe {
            let handles = core::slice::from_raw_parts(handles_ptr, len);
            let values = core::slice::from_raw_parts_mut(values_ptr, len);
            (handles, values)
        }
    }

    /// Returns [`true`] if the specified handle is valid for this pool.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::PackedInlinePool;
    /// let mut pool = PackedInlinePool::<u128, 16>::new();
    /// let h = pool.insert(0xF0E1_D2C3_B4A5_9687);
    /// assert!(pool.contains(h));
    /// assert_eq!(pool.remove(h), Some(0xF0E1_D2C3_B4A5_9687));
    /// assert!(!pool.contains(h));
    /// ```
    pub fn contains(&self, handle: H) -> bool {
        let (idx, input_gen_count) = handle.into_raw_parts();
        if idx >= self.buf.capacity() {
            return false;
        }

        let current_gen_count = unsafe { self.counters().add(idx).read() };
        current_gen_count == input_gen_count && current_gen_count % 2 == 1
    }

    /// Returns a reference to the value corresponding to the handle.
    ///
    /// Returns [`None`] if the handle is invalid for this pool.
    pub fn get(&self, handle: H) -> Option<&T> {
        let (index, input_gen_count) = handle.into_raw_parts();
        if index >= self.buf.capacity() {
            return None;
        }

        let current_gen_count = unsafe { self.counters().add(index).read() };
        if current_gen_count != input_gen_count || input_gen_count % 2 == 0 {
            return None;
        }

        let packed_index = unsafe {
            self.next_free_slot_or_packed_index_array()
                .add(index)
                .read()
        };
        unsafe { self.values_ptr().add(packed_index.as_usize()).as_ref() }
    }

    /// Returns a mutable reference to the value corresponding to the handle.
    ///
    /// Returns [`None`] if the handle is invalid for this pool.
    pub fn get_mut(&mut self, handle: H) -> Option<&mut T> {
        let (index, input_gen_count) = handle.into_raw_parts();
        if index >= self.buf.capacity() {
            return None;
        }

        let current_gen_count = unsafe { self.counters().add(index).read() };
        if current_gen_count != input_gen_count || input_gen_count % 2 == 0 {
            return None;
        }

        let packed_index = unsafe {
            self.next_free_slot_or_packed_index_array()
                .add(index)
                .read()
        };
        unsafe { self.values_mut_ptr().add(packed_index.as_usize()).as_mut() }
    }

    /// Returns mutable references to the values corresponding to the specified
    /// handles.
    ///
    /// Returns [`None`] if any of the handles are invalid, or if any two of
    /// them are equal to each other.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::PackedInlinePool;
    /// let mut pool = PackedInlinePool::<&'static str, 5>::new();
    /// let ha = pool.insert("apple");
    /// let hb = pool.insert("berry");
    /// let hc = pool.insert("coconut");
    ///
    /// assert!(pool.get_disjoint_mut([ha, ha]).is_none());
    ///
    /// if let Some([a, c]) = pool.get_disjoint_mut([ha, hc]) {
    ///     core::mem::swap(a, c);
    /// }
    ///
    /// assert_eq!(pool.get(ha), Some(&"coconut"));
    /// assert_eq!(pool.get(hb), Some(&"berry"));
    /// assert_eq!(pool.get(hc), Some(&"apple"));
    /// ```
    pub fn get_disjoint_mut<const N: usize>(&mut self, handles: [H; N]) -> Option<[&mut T; N]> {
        let mut result: [MaybeUninit<*mut T>; N] = unsafe { MaybeUninit::uninit().assume_init() };

        let counters = self.counters_mut();
        let slots = self.next_free_slot_or_packed_index_array();
        let values = self.values_mut_ptr();

        let mut i = 0;
        while i < N {
            let (index, input_gen_count) = handles[i].into_raw_parts();
            if index >= self.capacity() || input_gen_count % 2 == 0 {
                break;
            }

            let current_gen_count = unsafe { counters.add(index).read() };
            if current_gen_count != input_gen_count {
                break;
            }

            unsafe {
                *counters.add(index) ^= 1;
                let packed_index = slots.add(index).read().as_usize();
                result[i] = MaybeUninit::new(values.add(packed_index));
            }

            i += 1;
        }

        for h in &handles[..i] {
            let (index, _) = h.into_raw_parts();
            unsafe { *counters.add(index) ^= 1 };
        }

        if i == N {
            Some(unsafe { core::mem::transmute_copy(&result) })
        } else {
            None
        }
    }

    /// Inserts a value into the pool, returning a unique handle to access it.
    ///
    /// Returns `Err(value)` if the pool is already at capacity.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::PackedInlinePool;
    /// let mut pool = PackedInlinePool::<u16, 8>::new();
    /// let h = pool.try_insert(42).expect("failed to insert into an empty pool?!");
    /// assert_eq!(pool.get(h), Some(&42));
    /// ```
    pub fn try_insert(&mut self, value: T) -> Result<H, T> {
        let insert_position = self.next_free_slot.as_usize();
        if insert_position == Self::FREE_LIST_SENTINEL {
            return Err(value);
        }

        let packed_insert_position = self.len;
        self.len = H::Index::from_usize(packed_insert_position.as_usize() + 1);

        unsafe {
            let gen_count_ptr = self.counters_mut().add(insert_position);
            let gen_count = gen_count_ptr.read().wrapping_add(1) & H::MAX_GENERATION;
            debug_assert_eq!(gen_count % 2, 1);
            gen_count_ptr.write(gen_count);

            let slot_ptr = self
                .next_free_slot_or_packed_index_array_mut()
                .add(insert_position);
            self.next_free_slot = slot_ptr.read();
            slot_ptr.write(packed_insert_position);

            let handle = H::new(insert_position, gen_count);
            self.handles_mut_ptr()
                .add(packed_insert_position.as_usize())
                .write(handle);
            self.values_mut_ptr()
                .add(packed_insert_position.as_usize())
                .write(value);

            Ok(handle)
        }
    }

    /// Inserts a value into the pool, returning a unique handle to access it.
    ///
    /// # Panics
    /// Panics if the pool is already full. See [`try_insert`](PackedPool::try_insert)
    /// for a checked version.
    pub fn insert(&mut self, value: T) -> H {
        #[cold]
        #[inline(never)]
        fn assert_failed() -> ! {
            panic!("pool is already at capacity")
        }

        let result = self.try_insert(value);
        match result {
            Ok(handle) => handle,
            Err(_) => assert_failed(),
        }
    }

    /// Inserts a value given by `f` into the pool. The handle where the value
    /// will be stored is passed into `f`. This is useful for storing values
    /// containing their own handle.
    ///
    /// Returns [`None`] if the pool is already full, without calling `f`.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::{pool::DefaultHandle, PackedInlinePool};
    /// let mut pool = PackedInlinePool::<(DefaultHandle, u16), 8>::new();
    /// let h = pool.try_insert_with_handle(|h| (h, 42)).expect("failed to insert into an empty pool?!");
    /// assert_eq!(pool.get(h), Some(&(h, 42)));
    /// ```
    pub fn try_insert_with_handle<F: FnOnce(H) -> T>(&mut self, f: F) -> Option<H> {
        let insert_position = self.next_free_slot.as_usize();
        if insert_position == Self::FREE_LIST_SENTINEL {
            return None;
        }

        let packed_insert_position = self.len;
        self.len = H::Index::from_usize(packed_insert_position.as_usize() + 1);

        unsafe {
            let gen_count_ptr = self.counters_mut().add(insert_position);
            let gen_count = gen_count_ptr.read().wrapping_add(1) & H::MAX_GENERATION;
            debug_assert_eq!(gen_count % 2, 1);
            gen_count_ptr.write(gen_count);

            let slot_ptr = self
                .next_free_slot_or_packed_index_array_mut()
                .add(insert_position);
            self.next_free_slot = slot_ptr.read();
            slot_ptr.write(packed_insert_position);

            let handle = H::new(insert_position, gen_count);
            self.handles_mut_ptr()
                .add(packed_insert_position.as_usize())
                .write(handle);
            self.values_mut_ptr()
                .add(packed_insert_position.as_usize())
                .write(f(handle));

            Some(handle)
        }
    }

    /// Inserts a value given by `f` into the pool. The handle where the value
    /// will be stored is passed into `f`. This is useful for storing values
    /// containing their own handle.
    ///
    /// # Panics
    /// Panics if the pool is already full. See
    /// [`try_insert_with_handle`](PackedPool::try_insert_with_handle) for a
    /// checked version.
    pub fn insert_with_handle<F: FnOnce(H) -> T>(&mut self, f: F) -> H {
        self.try_insert_with_handle(f)
            .expect("pool is already at capacity")
    }

    /// Removes the value referred to by the specified handle from the pool,
    /// returning it unless the handle is invalid. This invalidates the handle.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::PackedInlinePool;
    /// let mut pool = PackedInlinePool::<u16, 8>::new();
    /// assert_eq!(pool.len(), 0);
    /// let h = pool.insert(42);
    /// assert_eq!(pool.len(), 1);
    /// assert_eq!(pool.remove(h), Some(42));
    /// assert_eq!(pool.len(), 0);
    /// assert_eq!(pool.remove(h), None);
    /// assert_eq!(pool.len(), 0);
    /// ```
    pub fn remove(&mut self, handle: H) -> Option<T> {
        let (index, input_gen_count) = handle.into_raw_parts();
        if index >= self.buf.capacity() || input_gen_count % 2 == 0 {
            return None;
        }

        let gen_count_ptr = unsafe { self.counters_mut().add(index) };
        let current_gen_count = unsafe { *gen_count_ptr };
        if current_gen_count != input_gen_count {
            return None;
        }

        unsafe {
            gen_count_ptr.write(current_gen_count.wrapping_add(1));

            let slot_ptr = self.next_free_slot_or_packed_index_array_mut().add(index);
            let packed_index = slot_ptr.read();
            slot_ptr.write(self.next_free_slot);
            self.next_free_slot = H::Index::from_usize(index);

            let hole = self.values_mut_ptr().add(packed_index.as_usize());
            let result = hole.read();

            let new_len = self.len() - 1;
            if new_len != packed_index.as_usize() {
                let last = self.values_ptr().add(new_len);
                core::ptr::copy(last, hole, 1);

                let hole = self.handles_mut_ptr().add(packed_index.as_usize());
                let last = self.handles_ptr().add(new_len);
                core::ptr::copy(last, hole, 1);

                let (index, _) = last.read().into_raw_parts();
                self.next_free_slot_or_packed_index_array_mut()
                    .add(index)
                    .write(packed_index);
            }

            self.len = H::Index::from_usize(new_len);
            Some(result)
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all handle-value pairs `(h, t)` such that
    /// `f(h, &mut t)` returns false. This method invalidates any removed
    /// handles.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::PackedInlinePool;
    /// let mut pool = PackedInlinePool::<u128, 4>::new();
    /// let h1 = pool.insert(1);
    /// let h2 = pool.insert(2);
    /// let h3 = pool.insert(3);
    /// pool.retain(|_, val| *val % 2 == 1);
    ///
    /// assert!(pool.contains(h1));
    /// assert!(!pool.contains(h2));
    /// assert!(pool.contains(h3));
    /// assert_eq!(pool.len(), 2);
    /// ```
    pub fn retain<F: FnMut(H, &mut T) -> bool>(&mut self, mut f: F) {
        self.drain_filter(|handle, item| !f(handle, item))
            .for_each(drop);
    }

    /// Clears the pool, dropping all values. This invalidates all handles.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::{pool::DefaultHandle, PackedInlinePool};
    /// let mut pool = PackedInlinePool::<u16, 5>::new();
    /// for i in 0..5 { pool.insert(i); }
    /// assert!(pool.is_full());
    ///
    /// pool.clear();
    /// assert!(pool.is_empty());
    /// ```
    pub fn clear(&mut self) {
        for packed_index in 0..self.len() {
            unsafe {
                self.values_mut_ptr().add(packed_index).drop_in_place();

                let (index, _) = self.handles_ptr().add(packed_index).read().into_raw_parts();
                *self.counters_mut().add(index) += 1;

                let slot_ptr = self.next_free_slot_or_packed_index_array_mut().add(index);
                *slot_ptr = self.next_free_slot;
                self.next_free_slot = H::Index::from_usize(index);
            }
        }

        self.len = H::Index::from_usize(0);
    }

    /// Creates an iterator visiting all handle-value pairs in arbitrary order,
    /// yielding `(H, &'a T)`.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::PackedInlinePool;
    /// let mut pool = PackedInlinePool::<u128, 5>::new();
    /// let h0 = pool.insert(0);
    /// let h1 = pool.insert(1);
    /// let h2 = pool.insert(2);
    ///
    /// let mut counts = [0, 0, 0];
    /// for (h, v) in pool.iter() {
    ///     if h == h0 && v == &0 { counts[0] += 1; }
    ///     else if h == h1 && v == &1 { counts[1] += 1; }
    ///     else if h == h2 && v == &2 { counts[2] += 1; }
    /// }
    ///
    /// assert_eq!(counts, [1, 1, 1]);
    /// ```
    pub fn iter(&self) -> Iter<'_, H, T> {
        Iter {
            handles: self.handles_ptr(),
            values: self.values_ptr(),
            len: self.len(),
            pool: PhantomData,
        }
    }

    /// Creates an iterator visiting all handle-value pairs in arbitrary order,
    /// yielding `(H, &'a mut T)`.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::PackedInlinePool;
    /// let mut pool = PackedInlinePool::<u128, 5>::new();
    /// let h1 = pool.insert(1);
    /// let h2 = pool.insert(2);
    /// let h3 = pool.insert(3);
    ///
    /// for (k, v) in pool.iter_mut() {
    ///     *v *= 2;
    /// }
    ///
    /// assert_eq!(pool[h1], 2);
    /// assert_eq!(pool[h2], 4);
    /// assert_eq!(pool[h3], 6);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, H, T> {
        IterMut {
            handles: self.handles_ptr(),
            values: self.values_mut_ptr(),
            len: self.len(),
            pool: PhantomData,
        }
    }

    /// Creates a draining iterator that removes all values from the pool and
    /// yields them and their handles in an arbitrary order.
    ///
    /// When the iterator **is** dropped, all remaining elements are removed
    /// from the pool, even if the iterator was not fully consumed. If the
    /// iterator **is not** dropped (with [`core::mem::forget`] for example),
    /// it is unspecified how many elements are removed.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::PackedInlinePool;
    /// let mut pool = PackedInlinePool::<u128, 5>::new();
    /// pool.insert(0);
    /// let mut it = pool.drain();
    /// assert!(matches!(it.next(), Some((_, 0))));
    /// assert!(it.next().is_none());
    /// drop(it);
    ///
    /// assert_eq!(pool.len(), 0);
    /// ```
    pub fn drain(&mut self) -> Drain<'_, T, S, H> {
        Drain { pool: self }
    }

    /// Creates an iterator which uses a closure to determine if an element
    /// should be removed.
    ///
    /// If the closure returns `true`, the element is removed and yielded with
    /// its handle. If the closure returns `false`, the element will remain in
    /// the pool and will not be yielded by the iterator.
    ///
    /// When the iterator **is** dropped, all remaining elements matching the
    /// filter are removed from the pool, even if the iterator was not fully
    /// consumed. If the iterator **is not** dropped (with [`core::mem::forget`]
    /// for example), it is unspecified how many such elements are removed.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::PackedInlinePool;
    /// let mut pool = PackedInlinePool::<u128, 10>::new();
    /// for i in 1..=10 {
    ///     pool.insert(i);
    /// }
    ///
    /// // filter out the even values:
    /// let mut it = pool.drain_filter(|_, val| *val % 2 == 0);
    /// for i in 1..=5 {
    ///     assert!(matches!(it.next(), Some((_, x)) if x % 2 == 0));
    /// }
    /// assert!(it.next().is_none());
    /// drop(it);
    ///
    /// assert_eq!(pool.len(), 5);
    /// ```
    pub fn drain_filter<F: FnMut(H, &mut T) -> bool>(
        &mut self,
        filter_fn: F,
    ) -> DrainFilter<'_, T, S, H, F> {
        let last_visited = self.len();
        DrainFilter {
            pool: self,
            last_visited,
            filter_fn,
        }
    }
}

impl<T, S: Storage<PackedPoolLayout<T, H>>, H: Handle> Index<H> for PackedPool<T, S, H> {
    type Output = T;
    fn index(&self, handle: H) -> &Self::Output {
        self.get(handle).expect("indexed with invalid pool handle")
    }
}

impl<T, S: Storage<PackedPoolLayout<T, H>>, H: Handle> IndexMut<H> for PackedPool<T, S, H> {
    fn index_mut(&mut self, handle: H) -> &mut Self::Output {
        self.get_mut(handle)
            .expect("indexed with invalid pool handle")
    }
}

impl<T, S: Storage<PackedPoolLayout<T, H>>, H: Handle> Drop for PackedPool<T, S, H> {
    fn drop(&mut self) {
        self.clear();
    }
}

struct DebugSlots<'a, T: Debug, S: Storage<PackedPoolLayout<T, H>>, H: Handle>(
    &'a PackedPool<T, S, H>,
);
impl<T: Debug, S: Storage<PackedPoolLayout<T, H>>, H: Handle> Debug for DebugSlots<'_, T, S, H> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> core::fmt::Result {
        let gen_count_ptr = self.0.counters();
        let slot_ptr = self.0.next_free_slot_or_packed_index_array();
        let values_ptr = self.0.values_ptr();
        fmt.debug_list()
            .entries(
                (0..self.0.capacity()).map::<DebugEntry<T, H>, _>(|i| unsafe {
                    let generation = gen_count_ptr.add(i).read();
                    if generation % 2 == 0 {
                        let next_free_slot = slot_ptr.add(i).read();
                        DebugEntry::Vacant {
                            generation,
                            next_free_slot,
                        }
                    } else {
                        let packed_index = slot_ptr.add(i).read().as_usize();
                        let value = &*values_ptr.add(packed_index);
                        DebugEntry::Occupied { generation, value }
                    }
                }),
            )
            .finish()
    }
}

impl<T: Debug, S: Storage<PackedPoolLayout<T, H>>, H: Handle> Debug for PackedPool<T, S, H> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> core::fmt::Result {
        let mut builder = fmt.debug_struct("PackedPool");
        builder
            .field("len", &self.len.as_usize())
            .field("next_free_slot", &self.next_free_slot.as_usize())
            .field("slots", &DebugSlots(self))
            .finish()
    }
}

/// An iterator visiting all handle-value pairs in a pool in arbitrary order, yielding `(H, &'a T)`.
///
/// This `struct` is created by [`PackedPool::iter`], see its documentation for more.
pub struct Iter<'a, H, T> {
    handles: *const H,
    values: *const T,
    len: usize,
    pool: PhantomData<&'a ()>,
}

impl<'a, H, T: 'a> Iterator for Iter<'a, H, T> {
    type Item = (H, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        Some(unsafe {
            let handle = self.handles.add(self.len).read();
            let value = &*self.values.add(self.len);
            (handle, value)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T: 'a, H> ExactSizeIterator for Iter<'a, H, T> {}
impl<'a, T: 'a, H> FusedIterator for Iter<'a, H, T> {}

impl<'a, T: 'a, S: Storage<PackedPoolLayout<T, H>>, H: Handle> IntoIterator
    for &'a PackedPool<T, S, H>
{
    type Item = (H, &'a T);
    type IntoIter = Iter<'a, H, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator visiting all handle-value pairs in a pool in arbitrary order, yielding `(H, &'a mut T)`.
///
/// This `struct` is created by [`PackedPool::iter_mut`], see its documentation for more.
pub struct IterMut<'a, H, T> {
    handles: *const H,
    values: *mut T,
    len: usize,
    pool: PhantomData<&'a mut ()>,
}

impl<'a, H, T: 'a> Iterator for IterMut<'a, H, T> {
    type Item = (H, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        Some(unsafe {
            let handle = self.handles.add(self.len).read();
            let value = &mut *self.values.add(self.len);
            (handle, value)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T: 'a, H> ExactSizeIterator for IterMut<'a, H, T> {}
impl<'a, T: 'a, H> FusedIterator for IterMut<'a, H, T> {}

impl<'a, T: 'a, S: Storage<PackedPoolLayout<T, H>>, H: Handle> IntoIterator
    for &'a mut PackedPool<T, S, H>
{
    type Item = (H, &'a mut T);
    type IntoIter = IterMut<'a, H, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// A draining iterator over the elements of a [`PackedPool`].
///
/// This `struct` is created by [`PackedPool::drain`], see its documentation for more.
pub struct Drain<'a, T, S: Storage<PackedPoolLayout<T, H>>, H: Handle> {
    pool: &'a mut PackedPool<T, S, H>,
}

impl<'a, T, S: Storage<PackedPoolLayout<T, H>>, H: Handle> Iterator for Drain<'a, T, S, H> {
    type Item = (H, T);

    fn next(&mut self) -> Option<Self::Item> {
        let len = self.pool.len();
        if len == 0 {
            return None;
        }

        let new_len = len - 1;
        let handle = unsafe { self.pool.handles_ptr().add(new_len).read() };
        let value = unsafe { self.pool.values_ptr().add(new_len).read() };

        let (index, gen_count) = handle.into_raw_parts();
        unsafe {
            self.pool
                .counters_mut()
                .add(index)
                .write(gen_count.wrapping_add(1));
            self.pool
                .next_free_slot_or_packed_index_array_mut()
                .add(index)
                .write(self.pool.next_free_slot);
        }

        self.pool.next_free_slot = H::Index::from_usize(index);
        self.pool.len = H::Index::from_usize(new_len);
        Some((handle, value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.pool.len();
        (size, Some(size))
    }
}

impl<'a, T, S: Storage<PackedPoolLayout<T, H>>, H: Handle> Drop for Drain<'a, T, S, H> {
    fn drop(&mut self) {
        self.pool.clear();
    }
}

impl<'a, T, S: Storage<PackedPoolLayout<T, H>>, H: Handle> ExactSizeIterator
    for Drain<'a, T, S, H>
{
}
impl<'a, T, S: Storage<PackedPoolLayout<T, H>>, H: Handle> FusedIterator for Drain<'a, T, S, H> {}

/// An iterator which uses a closure to determine if an element should be removed.
///
/// This `struct` is created by [`PackedPool::drain_filter`], see its documentation for more.
pub struct DrainFilter<
    'a,
    T,
    S: Storage<PackedPoolLayout<T, H>>,
    H: Handle,
    F: FnMut(H, &mut T) -> bool,
> {
    pool: &'a mut PackedPool<T, S, H>,
    last_visited: usize,
    filter_fn: F,
}

impl<'a, T, S: Storage<PackedPoolLayout<T, H>>, H: Handle, F: FnMut(H, &mut T) -> bool> Iterator
    for DrainFilter<'a, T, S, H, F>
{
    type Item = (H, T);

    fn next(&mut self) -> Option<Self::Item> {
        while self.last_visited > 0 {
            self.last_visited -= 1;

            let handle = unsafe { self.pool.handles_ptr().add(self.last_visited).read() };
            let should_remove = unsafe {
                let value_ref = &mut *self.pool.values_mut_ptr().add(self.last_visited);
                (self.filter_fn)(handle, value_ref)
            };

            if !should_remove {
                continue;
            }
            let new_len = self.pool.len() - 1;
            let value = unsafe { self.pool.values_ptr().add(self.last_visited).read() };

            let (index, gen_count) = handle.into_raw_parts();
            unsafe {
                self.pool
                    .counters_mut()
                    .add(index)
                    .write(gen_count.wrapping_add(1));
                self.pool
                    .next_free_slot_or_packed_index_array_mut()
                    .add(index)
                    .write(self.pool.next_free_slot);

                if index != new_len {
                    let value_src = self.pool.values_ptr().add(new_len);
                    let value_dst = self.pool.values_mut_ptr().add(self.last_visited);
                    core::ptr::copy(value_src, value_dst, 1);

                    let handle_src = self.pool.handles_ptr().add(new_len);
                    let handle_dst = self.pool.handles_mut_ptr().add(self.last_visited);
                    core::ptr::copy(handle_src, handle_dst, 1);

                    let (index, _) = handle_src.read().into_raw_parts();
                    self.pool
                        .next_free_slot_or_packed_index_array_mut()
                        .add(index)
                        .write(H::Index::from_usize(self.last_visited));
                }
            }

            self.pool.len = H::Index::from_usize(new_len);
            return Some((handle, value));
        }

        None
    }
}

impl<'a, T, S: Storage<PackedPoolLayout<T, H>>, H: Handle, F: FnMut(H, &mut T) -> bool> Drop
    for DrainFilter<'a, T, S, H, F>
{
    fn drop(&mut self) {
        self.for_each(drop);
    }
}

impl<'a, T, S: Storage<PackedPoolLayout<T, H>>, H: Handle, F: FnMut(H, &mut T) -> bool>
    ExactSizeIterator for DrainFilter<'a, T, S, H, F>
{
}
impl<'a, T, S: Storage<PackedPoolLayout<T, H>>, H: Handle, F: FnMut(H, &mut T) -> bool>
    FusedIterator for DrainFilter<'a, T, S, H, F>
{
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<T, H: Handle> crate::collections::PackedAllocPool<T, H> {
    /// Constructs a new, empty [`PackedAllocPool`](crate::collections::PackedAllocPool)
    /// with the specified capacity.
    ///
    /// # Panics
    /// Panics if the specified capacity is greater than or equal to `H::MAX_INDEX`.
    pub fn with_capacity(capacity: H::Index) -> Self {
        let cap = capacity.as_usize();
        if cap >= H::MAX_INDEX {
            buffer_too_large_for_handle_type::<H>();
        }

        let storage = crate::storage::AllocStorage::with_capacity(cap);
        Self::from(storage)
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<T: Clone, H: Handle> Clone for crate::collections::PackedAllocPool<T, H> {
    fn clone(&self) -> Self {
        let storage = crate::storage::AllocStorage::with_capacity(self.capacity());
        let mut result: Self = PackedPool {
            buf: storage,
            len: self.len,
            next_free_slot: self.next_free_slot,
            items: PhantomData,
        };

        for i in 0..self.len() {
            unsafe {
                let src = &*self.values_ptr().add(i);
                let dst = result.values_mut_ptr().add(i);
                dst.write(src.clone());
            }
        }

        let src_handles = self.handles_ptr();
        let dst_handles = result.handles_mut_ptr();
        unsafe { core::ptr::copy(src_handles, dst_handles, self.len()) };

        let src_counters = self.counters();
        let dst_counters = result.counters_mut();
        unsafe { core::ptr::copy(src_counters, dst_counters, self.capacity()) };

        let src_slots = self.next_free_slot_or_packed_index_array();
        let dst_slots = result.next_free_slot_or_packed_index_array_mut();
        unsafe { core::ptr::copy(src_slots, dst_slots, self.capacity()) };

        result
    }
}

/// A statically-sized storage block for a [`PackedPool`].
#[repr(C)]
pub struct InlineStorage<T, H: Handle, const N: usize> {
    // densely packed arrays:
    values: [MaybeUninit<T>; N],
    handles: [MaybeUninit<H>; N],
    // indices for random access:
    counters: [MaybeUninit<u32>; N],
    next_free_slot_or_packed_index: [MaybeUninit<H::Index>; N],
}

unsafe impl<T, H: Handle, const N: usize> Storage<PackedPoolLayout<T, H>>
    for InlineStorage<T, H, N>
{
    const MIN_REPRESENTABLE: usize = N;
    fn get_ptr(&self) -> *const u8 {
        (self as *const Self).cast()
    }
    fn get_mut_ptr(&mut self) -> *mut u8 {
        (self as *mut Self).cast()
    }
    fn capacity(&self) -> usize {
        N
    }
}

impl<T, H: Handle, const N: usize> PackedPool<T, InlineStorage<T, H, N>, H> {
    /// Constructs a new, empty `DirectPool` backed by [`InlineStorage`].
    pub fn new() -> Self {
        if N >= H::MAX_INDEX {
            buffer_too_large_for_handle_type::<H>();
        }

        Self::from(InlineStorage {
            values: unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() },
            handles: [MaybeUninit::uninit(); N],
            counters: [MaybeUninit::uninit(); N],
            next_free_slot_or_packed_index: [MaybeUninit::uninit(); N],
        })
    }
}

impl<T, H: Handle, const N: usize> Default for PackedPool<T, InlineStorage<T, H, N>, H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone, H: Handle, const N: usize> Clone for PackedPool<T, InlineStorage<T, H, N>, H> {
    fn clone(&self) -> Self {
        let mut result: Self = PackedPool {
            buf: InlineStorage {
                values: unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() },
                handles: [MaybeUninit::uninit(); N],
                counters: [MaybeUninit::uninit(); N],
                next_free_slot_or_packed_index: [MaybeUninit::uninit(); N],
            },
            len: self.len,
            next_free_slot: self.next_free_slot,
            items: PhantomData,
        };

        for i in 0..self.len() {
            unsafe {
                let src = self.values_ptr().add(i).as_ref().unwrap();
                let dst = result.values_mut_ptr().add(i);
                dst.write(src.clone());
            }
        }

        let src_handles = self.handles_ptr();
        let dst_handles = result.handles_mut_ptr();
        unsafe { core::ptr::copy(src_handles, dst_handles, self.len()) };

        let src_counters = self.counters();
        let dst_counters = result.counters_mut();
        unsafe { core::ptr::copy(src_counters, dst_counters, self.capacity()) };

        let src_slots = self.next_free_slot_or_packed_index_array();
        let dst_slots = result.next_free_slot_or_packed_index_array_mut();
        unsafe { core::ptr::copy(src_slots, dst_slots, self.capacity()) };

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::collections::pool::{DefaultHandle, Handle};
    use crate::storage::LayoutSpec;
    use crate::{arena::Arena, fmt};

    #[test]
    fn debug_impl() {
        let mut storage = [MaybeUninit::uninit(); 2048];
        let mut arena = Arena::from(&mut storage[..]);
        let mut pool: crate::collections::PackedArenaPool<&'static str, DefaultHandle> =
            arena.with_capacity(4);

        let empty = fmt!(arena, "{:?}", pool).unwrap();
        assert_eq!(
            &*empty,
            "PackedPool { len: 0, next_free_slot: 0, slots: [\
                Vacant { generation: 0, next_free_slot: 1 }, \
                Vacant { generation: 0, next_free_slot: 2 }, \
                Vacant { generation: 0, next_free_slot: 3 }, \
                Vacant { generation: 0, next_free_slot: 4294967295 }\
            ] }"
        );

        let h1 = pool.insert("First");
        pool.insert("Second");
        let h3 = pool.insert("Third");
        pool.insert("Fourth");

        let full = fmt!(&mut arena, "{:?}", pool).unwrap();
        assert_eq!(
            &*full,
            "PackedPool { len: 4, next_free_slot: 4294967295, slots: [\
                Occupied { generation: 1, value: \"First\" }, \
                Occupied { generation: 1, value: \"Second\" }, \
                Occupied { generation: 1, value: \"Third\" }, \
                Occupied { generation: 1, value: \"Fourth\" }\
            ] }"
        );

        pool.remove(h1);
        pool.remove(h3);

        let partial = fmt!(&mut arena, "{:?}", pool).unwrap();
        assert_eq!(
            &*partial,
            "PackedPool { len: 2, next_free_slot: 2, slots: [\
                Vacant { generation: 2, next_free_slot: 4294967295 }, \
                Occupied { generation: 1, value: \"Second\" }, \
                Vacant { generation: 2, next_free_slot: 0 }, \
                Occupied { generation: 1, value: \"Fourth\" }\
            ] }"
        );
    }

    #[test]
    fn inline_storage_layout() {
        fn test_layout<T, H: Handle, const N: usize>() {
            use core::alloc::Layout;
            let inline_layout = Layout::new::<InlineStorage<T, H, N>>();
            let dynamic_layout = PackedPoolLayout::<T, H>::layout_with_capacity(N).unwrap();

            assert_eq!(inline_layout, dynamic_layout);
        }

        test_layout::<[u8; 3], DefaultHandle, 10>();
        test_layout::<[u8; 25], DefaultHandle, 20>();
        test_layout::<u128, DefaultHandle, 40>();
        test_layout::<crate::collections::ArenaDeque<u8>, DefaultHandle, 80>();
    }
}
