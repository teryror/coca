//! Object pools with direct indexing using stable handles.
//!
//! Values are stored in an incontiguously populated array. This optimizes for
//! random access at the cost of iteration speed.

use core::alloc::{Layout, LayoutError};
use core::fmt::{Debug, Formatter};
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ops::{Index, IndexMut};

use super::{buffer_too_large_for_handle_type, DebugEntry, DefaultHandle, Handle};
use crate::storage::{Capacity, LayoutSpec, Storage};

union Slot<T, I: Capacity> {
    item: ManuallyDrop<T>,
    next_free_slot: I,
}

/// The [`LayoutSpec`] for a [`DirectPool`].
pub struct DirectPoolLayout<T, H>(PhantomData<(T, H)>);
impl<T, H: Handle> LayoutSpec for DirectPoolLayout<T, H> {
    fn layout_with_capacity(items: usize) -> Result<Layout, LayoutError> {
        let item_array = Layout::array::<Slot<T, H::Index>>(items)?;
        let gen_count_array = Layout::array::<u32>(items)?;
        let (extended, _) = item_array.extend(gen_count_array)?;
        Ok(extended.pad_to_align())
    }
}

/// A direct-mapped object pool with constant capacity.
///
/// See the [super module documentation](crate::collections::pool) for information on
/// pool-based memory management, and [this module's documentation](crate::collections::pool::direct)
/// for details on this variation of it.
pub struct DirectPool<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle = DefaultHandle> {
    buf: S,
    len: H::Index,
    next_free_slot: H::Index,
    items: PhantomData<T>,
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> From<S> for DirectPool<T, S, H> {
    fn from(buf: S) -> Self {
        let cap = buf.capacity();
        if cap >= H::MAX_INDEX {
            buffer_too_large_for_handle_type::<H>();
        }

        let mut result = DirectPool {
            buf,
            len: H::Index::from_usize(0),
            next_free_slot: H::Index::from_usize(0),
            items: PhantomData,
        };

        // initialize free list:
        let mut ptr = result.slots_mut();
        for i in 1..cap {
            unsafe {
                (*ptr).next_free_slot = H::Index::from_usize(i);
                ptr = ptr.add(1);
            }
        }

        let sentinel = H::Index::from_usize(Self::FREE_LIST_SENTINEL);
        unsafe { (*ptr).next_free_slot = sentinel; }

        // initialize generation counters:
        unsafe { core::ptr::write_bytes(result.gen_counts_mut(), 0x00, cap); }

        result
    }
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> DirectPool<T, S, H> {
    const FREE_LIST_SENTINEL: usize = H::Index::MAX_REPRESENTABLE;

    #[inline]
    fn slots(&self) -> *const Slot<T, H::Index> {
        self.buf.get_ptr().cast()
    }

    #[inline]
    fn gen_counts(&self) -> *const u32 {
        let cap = self.buf.capacity();
        let item_array = Layout::array::<Slot<T, H::Index>>(cap).unwrap();
        let gen_count_array = Layout::array::<u32>(cap).unwrap();
        let (_, offset) = item_array.extend(gen_count_array).unwrap();
        unsafe { self.buf.get_ptr().add(offset).cast() }
    }

    #[inline]
    fn slots_mut(&mut self) -> *mut Slot<T, H::Index> {
        self.buf.get_mut_ptr().cast()
    }

    #[inline]
    fn gen_counts_mut(&mut self) -> *mut u32 {
        let cap = self.buf.capacity();
        let item_array = Layout::array::<Slot<T, H::Index>>(cap).unwrap();
        let gen_count_array = Layout::array::<u32>(cap).unwrap();
        let (_, offset) = item_array.extend(gen_count_array).unwrap();
        unsafe { self.buf.get_mut_ptr().add(offset).cast() }
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
        self.len.as_usize() == 0
    }

    /// Returns [`true`] if the pool contains the maximum number of elements.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len.as_usize() == self.buf.capacity()
    }

    /// Returns [`true`] if the specified handle is valid for this pool.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::{pool::DefaultHandle, DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::arena::Arena::from(&mut backing[..]);
    /// let mut pool: DirectArenaPool<u128, DefaultHandle> = arena.with_capacity(8);
    /// let h = pool.insert(0xDEAD_BEEF);
    /// assert!(pool.contains(h));
    /// pool.remove(h);
    /// assert!(!pool.contains(h));
    /// ```
    pub fn contains(&self, handle: H) -> bool {
        let (index, input_gen_count) = handle.into_raw_parts();
        if index >= self.buf.capacity() {
            return false;
        }
        let current_gen_count = unsafe { self.gen_counts().add(index).read() };
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
        let current_gen_count = unsafe { self.gen_counts().add(index).read() };
        if current_gen_count != input_gen_count || input_gen_count % 2 == 0 {
            return None;
        }
        unsafe { (self.slots().add(index).cast::<T>()).as_ref() }
    }

    /// Returns a mutable reference to the value corresponding to the handle.
    ///
    /// Returns [`None`] if the handle is invalid for this pool.
    pub fn get_mut(&mut self, handle: H) -> Option<&mut T> {
        let (index, input_gen_count) = handle.into_raw_parts();
        if index >= self.buf.capacity() {
            return None;
        }
        let current_gen_count = unsafe { self.gen_counts().add(index).read() };
        if current_gen_count != input_gen_count || input_gen_count % 2 == 0 {
            return None;
        }
        unsafe { (self.slots_mut().add(index).cast::<T>()).as_mut() }
    }

    /// Returns mutable references to the values corresponding to the specified
    /// handles.
    ///
    /// Returns [`None`] if any one of the handles is invalid, or if any two of
    /// them are equal to each other.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::{pool::DefaultHandle, DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::arena::Arena::from(&mut backing[..]);
    /// let mut pool: DirectArenaPool<&'static str, DefaultHandle> = arena.with_capacity(8);
    /// let ha = pool.insert("apple");
    /// let hb = pool.insert("berry");
    /// let hc = pool.insert("coconut");
    /// assert!(pool.get_disjoint_mut([ha, ha]).is_none());
    /// if let Some([a, c]) = pool.get_disjoint_mut([ha, hc]) {
    ///     core::mem::swap(a, c);
    /// }
    /// assert_eq!(pool[ha], "coconut");
    /// assert_eq!(pool[hc], "apple");
    /// ```
    pub fn get_disjoint_mut<const N: usize>(&mut self, handles: [H; N]) -> Option<[&mut T; N]> {
        let mut result: [MaybeUninit<*mut T>; N] = unsafe { MaybeUninit::uninit().assume_init() };

        let counters = self.gen_counts_mut();
        let slots = self.slots_mut();

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
                *counters.add(index) ^= 1; // Temporarily mark the slot as unoccupied for linear time disjointness check
                result[i] = MaybeUninit::new(slots.add(index).cast::<T>());
            }

            i += 1;
        }

        for h in &handles[..i] {
            let (index, _) = h.into_raw_parts();
            unsafe { *self.gen_counts_mut().add(index) ^= 1 };
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
    /// # use coca::collections::{pool::DefaultHandle, DirectArenaPool};
    /// # fn test() -> Result<(), u128> {
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::arena::Arena::from(&mut backing[..]);
    /// let mut pool: DirectArenaPool<u128, DefaultHandle> = arena.with_capacity(8);
    /// let h = pool.try_insert(42)?;
    /// assert_eq!(pool[h], 42);
    /// # Ok(())
    /// # }
    /// # assert!(test().is_ok());
    /// ```
    pub fn try_insert(&mut self, value: T) -> Result<H, T> {
        let insert_position = self.next_free_slot.as_usize();
        if insert_position == Self::FREE_LIST_SENTINEL {
            return Err(value);
        }

        self.len = H::Index::from_usize(self.len() + 1);
        unsafe {
            let gen_count_ptr = self.gen_counts_mut().add(insert_position);
            let gen_count = gen_count_ptr.read().wrapping_add(1) & H::MAX_GENERATION;
            debug_assert_eq!(gen_count % 2, 1);
            gen_count_ptr.write(gen_count);

            let slot = self.slots_mut().add(insert_position);
            self.next_free_slot = (*slot).next_free_slot;
            (*slot).item = ManuallyDrop::new(value);

            Ok(H::new(insert_position, gen_count))
        }
    }

    /// Inserts a value into the pool, returning a unique handle to access it.
    ///
    /// # Panics
    /// Panics if the pool is already full. See [`try_insert`](DirectPool::try_insert)
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
    /// # use coca::collections::{pool::DefaultHandle, DirectArenaPool};
    /// # fn test() -> Option<()> {
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::arena::Arena::from(&mut backing[..]);
    /// let mut pool: DirectArenaPool<(DefaultHandle, u64), DefaultHandle> = arena.with_capacity(10);
    /// let h = pool.insert_with_handle(|h| (h, 20));
    /// assert_eq!(pool[h], (h, 20));
    /// # Some(())
    /// # }
    /// # assert!(test().is_some());
    /// ```
    pub fn try_insert_with_handle<F: FnOnce(H) -> T>(&mut self, f: F) -> Option<H> {
        let insert_position = self.next_free_slot.as_usize();
        if insert_position == Self::FREE_LIST_SENTINEL {
            return None;
        }

        self.len = H::Index::from_usize(self.len() + 1);
        unsafe {
            let gen_count_ptr = self.gen_counts_mut().add(insert_position);
            let gen_count = gen_count_ptr.read().wrapping_add(1) & H::MAX_GENERATION;
            debug_assert_eq!(gen_count % 2, 1);
            gen_count_ptr.write(gen_count);

            let slot = self.slots_mut().add(insert_position);
            self.next_free_slot = (*slot).next_free_slot;
            let handle = H::new(insert_position, gen_count);

            (*slot).item = ManuallyDrop::new(f(handle));
            Some(handle)
        }
    }

    /// Inserts a value given by `f` into the pool. The handle where the value
    /// will be stored is passed into `f`. This is useful for storing values
    /// containing their own handle.
    ///
    /// # Panics
    /// Panics if the pool is already full. See
    /// [`try_insert_with_handle`](DirectPool::try_insert_with_handle) for a
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
    /// # use coca::collections::{pool::DefaultHandle, DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::arena::Arena::from(&mut backing[..]);
    /// let mut pool: DirectArenaPool<u128, DefaultHandle> = arena.with_capacity(8);
    /// let h = pool.insert(42);
    /// assert_eq!(pool.remove(h), Some(42));
    /// assert_eq!(pool.remove(h), None);
    /// ```
    pub fn remove(&mut self, handle: H) -> Option<T> {
        let (index, input_gen_count) = handle.into_raw_parts();
        if index >= self.buf.capacity() || input_gen_count % 2 == 0 {
            return None;
        }

        let gen_count_ptr = unsafe { self.gen_counts_mut().add(index) };
        let current_gen_count = unsafe { *gen_count_ptr };
        if current_gen_count != input_gen_count {
            return None;
        }

        self.len = H::Index::from_usize(self.len() - 1);
        let item = unsafe {
            *gen_count_ptr = current_gen_count.wrapping_add(1) & H::MAX_GENERATION;

            let slot_ptr = self.slots_mut().add(index);
            let item = slot_ptr.read().item;
            (*slot_ptr).next_free_slot = self.next_free_slot;

            item
        };
        self.next_free_slot = H::Index::from_usize(index);
        Some(ManuallyDrop::into_inner(item))
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all handle-value pairs `(h, t)` such that
    /// `f(h, &mut t)` returns false. This method invalidates any removed
    /// handles.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::{pool::DefaultHandle, DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::arena::Arena::from(&mut backing[..]);
    /// let mut pool: DirectArenaPool<u128, DefaultHandle> = arena.with_capacity(4);
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
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::{pool::DefaultHandle, DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::arena::Arena::from(&mut backing[..]);
    /// let mut pool: DirectArenaPool<u128, DefaultHandle> = arena.with_capacity(5);
    /// for i in 0..5 {
    ///     pool.insert(i);
    /// }
    ///
    /// assert!(pool.is_full());
    /// pool.clear();
    /// assert!(pool.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.drain().for_each(drop);
    }

    /// Creates an iterator visiting all handle-value pairs in arbitrary order,
    /// yielding `(H, &'a T)`.
    ///
    /// This iterator must visit all slots, empty or not. In the face of many
    /// deleted elements it can be inefficient.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::{pool::DefaultHandle, DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::arena::Arena::from(&mut backing[..]);
    /// let mut pool: DirectArenaPool<u128, DefaultHandle> = arena.with_capacity(5);
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
    pub fn iter(&self) -> Iter<'_, T, S, H> {
        Iter {
            pool: self,
            front: H::Index::from_usize(0),
            visited: H::Index::from_usize(0),
        }
    }

    /// Creates an iterator visiting all handle-value pairs in arbitrary order,
    /// yielding `(H, &'a mut T)`.
    ///
    /// This iterator must visit all slots, empty or not. In the face of many
    /// deleted elements it can be inefficient.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::{pool::DefaultHandle, DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::arena::Arena::from(&mut backing[..]);
    /// let mut pool: DirectArenaPool<u128, DefaultHandle> = arena.with_capacity(5);
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
    pub fn iter_mut(&mut self) -> IterMut<'_, T, S, H> {
        IterMut {
            pool: self,
            front: H::Index::from_usize(0),
            visited: H::Index::from_usize(0),
        }
    }

    /// Creates an iterator yielding all valid handles in arbitrary order.
    ///
    /// This iterator must visit all slots, empty or not. In the face of many
    /// deleted elements it can be inefficient.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::{pool::DefaultHandle, DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::arena::Arena::from(&mut backing[..]);
    /// let mut pool: DirectArenaPool<u128, DefaultHandle> = arena.with_capacity(5);
    /// assert!(pool.handles().next().is_none());
    ///
    /// let h0 = pool.insert(10);
    /// let h1 = pool.insert(20);
    /// let h2 = pool.insert(30);
    ///
    /// let mut counts = [0, 0, 0];
    /// for handle in pool.handles() {
    ///     if handle == h0 { counts[0] += 1; }
    ///     else if handle == h1 { counts[1] += 1; }
    ///     else if handle == h2 { counts[2] += 1; }
    /// }
    ///
    /// assert_eq!(counts, [1, 1, 1]);
    /// ```
    pub fn handles(&self) -> Handles<'_, T, S, H> {
        Handles { iter: self.iter() }
    }

    /// Creates an iterator yielding references to all stored values in arbitrary order.
    ///
    /// This iterator must visit all slots, empty or not. In the face of many
    /// deleted elements it can be inefficient.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::{pool::DefaultHandle, DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::arena::Arena::from(&mut backing[..]);
    /// let mut pool: DirectArenaPool<u128, DefaultHandle> = arena.with_capacity(5);
    /// assert!(pool.values().next().is_none());
    ///
    /// let h0 = pool.insert(10);
    /// let h1 = pool.insert(20);
    /// let h2 = pool.insert(30);
    ///
    /// let mut counts = [0, 0, 0];
    /// for value in pool.values() {
    ///     if *value == 10 { counts[0] += 1; }
    ///     else if *value == 20 { counts[1] += 1; }
    ///     else if *value == 30 { counts[2] += 1; }
    /// }
    ///
    /// assert_eq!(counts, [1, 1, 1]);
    /// ```
    pub fn values(&self) -> Values<'_, T, S, H> {
        Values { iter: self.iter() }
    }

    /// Creates an iterator yielding mutable references to all stored values
    /// in arbitrary order.
    ///
    /// This iterator must visit all slots, empty or not. In the face of many
    /// deleted elements it can be inefficient.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::{pool::DefaultHandle, DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::arena::Arena::from(&mut backing[..]);
    /// let mut pool: DirectArenaPool<u128, DefaultHandle> = arena.with_capacity(5);
    /// assert!(pool.values_mut().next().is_none());
    ///
    /// let h0 = pool.insert(10);
    /// let h1 = pool.insert(20);
    /// let h2 = pool.insert(30);
    /// pool.values_mut().for_each(|n| *n *= 2);
    ///
    /// assert_eq!(pool[h0], 20);
    /// assert_eq!(pool[h1], 40);
    /// assert_eq!(pool[h2], 60);
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, T, S, H> {
        ValuesMut {
            iter: self.iter_mut(),
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
    /// This iterator must visit all slots, empty or not. In the face of many
    /// deleted elements it can be inefficient.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::{pool::DefaultHandle, DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::arena::Arena::from(&mut backing[..]);
    /// let mut pool: DirectArenaPool<u128, DefaultHandle> = arena.with_capacity(5);
    /// pool.insert(0);
    /// let mut it = pool.drain();
    /// assert!(matches!(it.next(), Some((_, 0))));
    /// assert!(it.next().is_none());
    /// drop(it);
    ///
    /// assert_eq!(pool.len(), 0);
    /// ```
    pub fn drain(&mut self) -> Drain<'_, T, S, H> {
        Drain {
            pool: self,
            front: H::Index::from_usize(0),
        }
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
    /// This iterator must visit all slots, empty or not. In the face of many
    /// deleted elements it can be inefficient.
    ///
    /// # Examples
    /// ```
    /// # use coca::collections::{pool::DefaultHandle, DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 2048];
    /// # let mut arena = coca::arena::Arena::from(&mut backing[..]);
    /// let mut pool: DirectArenaPool<u128, DefaultHandle> = arena.with_capacity(10);
    /// for i in 1..=10 {
    ///     pool.insert(i);
    /// }
    ///
    /// // filter out the even values:
    /// let mut it = pool.drain_filter(|_, val| *val % 2 == 0);
    /// for i in 1..=5 {
    ///     assert!(matches!(it.next(), Some((_, x)) if x == 2 * i));
    /// }
    /// assert!(it.next().is_none());
    /// drop(it);
    ///
    /// assert_eq!(pool.len(), 5);
    /// ```
    pub fn drain_filter<F: FnMut(H, &mut T) -> bool>(
        &mut self,
        filter: F,
    ) -> DrainFilter<'_, T, S, H, F> {
        DrainFilter {
            pool: self,
            filter_fn: filter,
            front: H::Index::from_usize(0),
            kept: H::Index::from_usize(0),
        }
    }
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> Index<H> for DirectPool<T, S, H> {
    type Output = T;

    fn index(&self, handle: H) -> &Self::Output {
        self.get(handle).expect("indexed with invalid pool handle")
    }
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> IndexMut<H> for DirectPool<T, S, H> {
    fn index_mut(&mut self, handle: H) -> &mut Self::Output {
        self.get_mut(handle)
            .expect("indexed with invalid pool handle")
    }
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> Drop for DirectPool<T, S, H> {
    fn drop(&mut self) {
        let mut num_to_drop = self.len();
        let item_ptr = self.slots_mut();
        let gen_ptr = self.gen_counts();

        for i in 0..self.capacity() {
            unsafe {
                if gen_ptr.add(i).read() % 2 == 1 {
                    ManuallyDrop::drop((item_ptr.add(i).cast::<ManuallyDrop<T>>()).as_mut().unwrap());
                    num_to_drop -= 1;
                }
            }
            if num_to_drop == 0 {
                break;
            }
        }
    }
}

struct DebugSlots<'a, T: Debug, S: Storage<DirectPoolLayout<T, H>>, H: Handle>(
    &'a DirectPool<T, S, H>,
);
impl<T: Debug, S: Storage<DirectPoolLayout<T, H>>, H: Handle> Debug for DebugSlots<'_, T, S, H> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> core::fmt::Result {
        let gen_count_ptr = self.0.gen_counts();
        let slot_ptr = self.0.slots();
        fmt.debug_list()
            .entries(
                (0..self.0.capacity()).map::<DebugEntry<T, H>, _>(|i| unsafe {
                    let generation = gen_count_ptr.add(i).read();
                    if generation % 2 == 0 {
                        let next_free_slot = (*slot_ptr.add(i)).next_free_slot;
                        DebugEntry::Vacant {
                            generation,
                            next_free_slot,
                        }
                    } else {
                        let value = (slot_ptr.add(i).cast::<T>()).as_ref().unwrap();
                        DebugEntry::Occupied { generation, value }
                    }
                }),
            )
            .finish()
    }
}

impl<T: Debug, S: Storage<DirectPoolLayout<T, H>>, H: Handle> Debug for DirectPool<T, S, H> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> core::fmt::Result {
        let mut builder = fmt.debug_struct("DirectPool");
        builder
            .field("len", &self.len.as_usize())
            .field("next_free_slot", &self.next_free_slot.as_usize())
            .field("slots", &DebugSlots(self))
            .finish()
    }
}

/// An iterator visiting all handle-value pairs in a pool in arbitrary order, yielding `(H, &'a T)`.
///
/// This `struct` is created by [`DirectPool::iter`], see its documentation for more.
pub struct Iter<'a, T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> {
    pool: &'a DirectPool<T, S, H>,
    front: H::Index,
    visited: H::Index,
}

impl<'a, T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> Iterator for Iter<'a, T, S, H> {
    type Item = (H, &'a T);
    fn next(&mut self) -> Option<Self::Item> {
        if self.visited == self.pool.len {
            return None;
        }

        let gen_count_ptr = self.pool.gen_counts();
        let item_ptr = self.pool.slots();

        for i in self.front.as_usize()..self.pool.capacity() {
            let gen_count = unsafe { gen_count_ptr.add(i).read() };
            if gen_count % 2 == 0 {
                continue;
            }

            self.visited = H::Index::from_usize(self.visited.as_usize() + 1);
            self.front = H::Index::from_usize(i + 1);
            unsafe {
                let handle = H::new(i, gen_count);
                let item = (item_ptr.add(i).cast::<T>()).as_ref().unwrap();
                return Some((handle, item));
            }
        }

        unreachable!("internal error: mismatch between pool.len and number of occupied slots")
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.pool.len() - self.visited.as_usize();
        (len, Some(len))
    }
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> ExactSizeIterator for Iter<'_, T, S, H> {}
impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> FusedIterator for Iter<'_, T, S, H> {}

impl<'a, T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> IntoIterator
    for &'a DirectPool<T, S, H>
{
    type IntoIter = Iter<'a, T, S, H>;
    type Item = (H, &'a T);
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator visiting all handle-value pairs in a pool in arbitrary order, yielding `(H, &'a mut T)`.
///
/// This `struct` is created by [`DirectPool::iter_mut`], see its documentation for more.
pub struct IterMut<'a, T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> {
    pool: &'a mut DirectPool<T, S, H>,
    front: H::Index,
    visited: H::Index,
}

impl<'a, T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> Iterator for IterMut<'a, T, S, H> {
    type Item = (H, &'a mut T);
    fn next(&mut self) -> Option<Self::Item> {
        if self.visited == self.pool.len {
            return None;
        }

        let gen_count_ptr = self.pool.gen_counts();
        let item_ptr = self.pool.slots_mut();

        for i in self.front.as_usize()..self.pool.capacity() {
            let gen_count = unsafe { gen_count_ptr.add(i).read() };
            if gen_count % 2 == 0 {
                continue;
            }

            self.visited = H::Index::from_usize(self.visited.as_usize() + 1);
            self.front = H::Index::from_usize(i + 1);
            unsafe {
                let handle = H::new(i, gen_count);
                let item = (item_ptr.add(i).cast::<T>()).as_mut().unwrap();
                return Some((handle, item));
            }
        }

        unreachable!("internal error: mismatch between pool.len and number of occupied slots")
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.pool.len() - self.visited.as_usize();
        (len, Some(len))
    }
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> ExactSizeIterator for IterMut<'_, T, S, H> {}
impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> FusedIterator for IterMut<'_, T, S, H> {}

impl<'a, T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> IntoIterator
    for &'a mut DirectPool<T, S, H>
{
    type IntoIter = IterMut<'a, T, S, H>;
    type Item = (H, &'a mut T);
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// An iterator over the valid handles in a pool.
///
/// This struct is created by [`DirectPool::handles`], see its documentation for more.
pub struct Handles<'a, T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> {
    iter: Iter<'a, T, S, H>,
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> Iterator for Handles<'_, T, S, H> {
    type Item = H;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(h, _)| h)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> ExactSizeIterator for Handles<'_, T, S, H> {}
impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> FusedIterator for Handles<'_, T, S, H> {}

/// An iterator yielding references to all values in a pool.
///
/// This struct is created by [`DirectPool::values`], see its documentation for more.
pub struct Values<'a, T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> {
    iter: Iter<'a, T, S, H>,
}

impl<'a, T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> Iterator for Values<'a, T, S, H> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(_, item)| item)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> ExactSizeIterator for Values<'_, T, S, H> {}
impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> FusedIterator for Values<'_, T, S, H> {}

/// An iterator yielding mutable references to all values in a pool.
///
/// This struct is created by [`DirectPool::values_mut`], see its documentation for more.
pub struct ValuesMut<'a, T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> {
    iter: IterMut<'a, T, S, H>,
}

impl<'a, T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> Iterator for ValuesMut<'a, T, S, H> {
    type Item = &'a mut T;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(_, item)| item)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> ExactSizeIterator
    for ValuesMut<'_, T, S, H>
{
}
impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> FusedIterator for ValuesMut<'_, T, S, H> {}

/// A draining iterator over the elements of a [`DirectPool`].
///
/// This `struct` is created by [`DirectPool::drain`], see its documentation for more.
pub struct Drain<'a, T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> {
    pool: &'a mut DirectPool<T, S, H>,
    front: H::Index,
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> Iterator for Drain<'_, T, S, H> {
    type Item = (H, T);
    fn next(&mut self) -> Option<Self::Item> {
        if self.pool.is_empty() {
            return None;
        }

        let gen_count_ptr = self.pool.gen_counts_mut();
        let item_ptr = self.pool.slots_mut();

        for i in self.front.as_usize()..self.pool.capacity() {
            let gen_count = unsafe { gen_count_ptr.add(i).read() };
            if gen_count % 2 == 0 {
                continue;
            }

            self.front = H::Index::from_usize(i + 1);
            self.pool.len = H::Index::from_usize(self.pool.len() - 1);
            let new_gen_count = gen_count.wrapping_add(1) & H::MAX_GENERATION;

            unsafe {
                let handle = H::new(i, gen_count);
                gen_count_ptr.add(i).write(new_gen_count);
                let result = (item_ptr.add(i).cast::<T>()).read();
                (*item_ptr.add(i)).next_free_slot = self.pool.next_free_slot;
                self.pool.next_free_slot = H::Index::from_usize(i);

                return Some((handle, result));
            }
        }

        unreachable!("internal error: mismatch between pool.len and number of occupied slots");
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.pool.len();
        (size, Some(size))
    }
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> Drop for Drain<'_, T, S, H> {
    fn drop(&mut self) {
        self.for_each(drop);
    }
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> ExactSizeIterator for Drain<'_, T, S, H> {}
impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> FusedIterator for Drain<'_, T, S, H> {}

/// An iterator which uses a closure to determine if an element should be removed.
///
/// This `struct` is created by [`DirectPool::drain_filter`], see its documentation for more.
#[derive(Debug)]
pub struct DrainFilter<
    'a,
    T,
    S: Storage<DirectPoolLayout<T, H>>,
    H: Handle,
    F: FnMut(H, &mut T) -> bool,
> {
    pool: &'a mut DirectPool<T, S, H>,
    filter_fn: F,
    front: H::Index,
    kept: H::Index,
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle, F: FnMut(H, &mut T) -> bool> Iterator
    for DrainFilter<'_, T, S, H, F>
{
    type Item = (H, T);
    fn next(&mut self) -> Option<Self::Item> {
        let gen_count_ptr = self.pool.gen_counts_mut();
        let item_ptr = self.pool.slots_mut();

        for i in self.front.as_usize()..self.pool.capacity() {
            if self.kept == self.pool.len {
                self.front = H::Index::from_usize(i);
                break;
            }

            let gen_count = unsafe { gen_count_ptr.add(i).read() };
            if gen_count % 2 == 0 {
                continue;
            }

            let handle = unsafe { H::new(i, gen_count) };
            let item = unsafe { (item_ptr.add(i).cast::<T>()).as_mut().unwrap() };
            if !(self.filter_fn)(handle, item) {
                self.kept = H::Index::from_usize(self.kept.as_usize() + 1);
                continue;
            }

            self.front = H::Index::from_usize(i + 1);
            self.pool.len = H::Index::from_usize(self.pool.len() - 1);
            let gen_count = gen_count.wrapping_add(1) & H::MAX_GENERATION;

            unsafe {
                gen_count_ptr.add(i).write(gen_count);
                let result = (item_ptr.add(i).cast::<T>()).read();
                (*item_ptr.add(i)).next_free_slot = self.pool.next_free_slot;
                self.pool.next_free_slot = H::Index::from_usize(i);

                return Some((handle, result));
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.pool.len() - self.kept.as_usize();
        (0, Some(remaining))
    }
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle, F: FnMut(H, &mut T) -> bool> Drop
    for DrainFilter<'_, T, S, H, F>
{
    fn drop(&mut self) {
        self.for_each(drop);
    }
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle, F: FnMut(H, &mut T) -> bool> FusedIterator
    for DrainFilter<'_, T, S, H, F>
{
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<T, H: Handle> crate::collections::DirectAllocPool<T, H> {
    /// Constructs a new, empty [`DirectAllocPool`](crate::collections::DirectAllocPool)
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
impl<T: Clone, H: Handle> Clone for crate::collections::DirectAllocPool<T, H> {
    fn clone(&self) -> Self {
        let storage = crate::storage::AllocStorage::with_capacity(self.capacity());
        let mut result = DirectPool {
            buf: storage,
            len: self.len,
            next_free_slot: self.next_free_slot,
            items: PhantomData,
        };

        let src_counts = self.gen_counts();
        let dst_counts = result.gen_counts_mut();
        unsafe { core::ptr::copy(src_counts, dst_counts, self.capacity()) };

        let src_slots = self.slots();
        let dst_slots = result.slots_mut();

        for i in 0..self.capacity() {
            unsafe {
                let generation = dst_counts.add(i).read();
                if generation % 2 == 1 {
                    let item = src_slots.add(i).cast::<T>().as_ref().unwrap();
                    dst_slots.add(i).cast::<T>().write(item.clone());
                } else {
                    let next_free_slot = (*src_slots.add(i)).next_free_slot;
                    (*dst_slots.add(i)).next_free_slot = next_free_slot;
                }
            }
        }

        result
    }
}

/// A statically-sized storage block for a [`DirectPool`].
#[repr(C)]
pub struct InlineStorage<T, H: Handle, const N: usize> {
    slots: core::mem::MaybeUninit<[Slot<T, H::Index>; N]>,
    counters: core::mem::MaybeUninit<[u32; N]>,
}

unsafe impl<T, H: Handle, const N: usize> Storage<DirectPoolLayout<T, H>>
    for InlineStorage<T, H, N>
{
    #[inline]
    fn get_ptr(&self) -> *const u8 {
        (self as *const Self).cast()
    }

    #[inline]
    fn get_mut_ptr(&mut self) -> *mut u8 {
        (self as *mut Self).cast()
    }

    #[inline]
    fn capacity(&self) -> usize {
        N
    }
}

impl<T, H: Handle, const N: usize> DirectPool<T, InlineStorage<T, H, N>, H> {
    /// Constructs a new, empty `DirectPool` backed by [`InlineStorage`].
    pub fn new() -> Self {
        if N >= H::MAX_INDEX {
            buffer_too_large_for_handle_type::<H>();
        }

        Self::from(InlineStorage {
            slots: core::mem::MaybeUninit::uninit(),
            counters: core::mem::MaybeUninit::uninit(),
        })
    }
}

impl<T, H: Handle, const N: usize> Default for DirectPool<T, InlineStorage<T, H, N>, H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone, H: Handle, const N: usize> Clone for DirectPool<T, InlineStorage<T, H, N>, H> {
    fn clone(&self) -> Self {
        let mut result = DirectPool {
            buf: InlineStorage {
                slots: MaybeUninit::uninit(),
                counters: MaybeUninit::uninit(),
            },
            len: self.len,
            next_free_slot: self.next_free_slot,
            items: PhantomData,
        };

        let src_counts = self.gen_counts();
        let dst_counts = result.gen_counts_mut();
        unsafe { core::ptr::copy(src_counts, dst_counts, self.capacity()); }

        let src_slots = self.slots();
        let dst_slots = result.slots_mut();

        for i in 0..self.capacity() {
            unsafe {
                let generation = dst_counts.add(i).read();
                if generation % 2 == 1 {
                    let item = (src_slots.add(i).cast::<T>()).as_ref().unwrap();
                    (dst_slots.add(i).cast::<T>()).write(item.clone());
                } else {
                    let next_free_slot = (*src_slots.add(i)).next_free_slot;
                    (*dst_slots.add(i)).next_free_slot = next_free_slot;
                }
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use core::mem::MaybeUninit;

    use super::*;
    use crate::collections::pool::{DefaultHandle, Handle};
    use crate::storage::LayoutSpec;
    use crate::{fmt, arena::Arena};

    #[test]
    fn inline_storage_layout() {
        fn test_layout<T, H: Handle, const N: usize>() {
            use core::alloc::Layout;
            let inline_layout = Layout::new::<InlineStorage<T, H, N>>();
            let dynamic_layout = DirectPoolLayout::<T, H>::layout_with_capacity(N).unwrap();

            assert_eq!(inline_layout, dynamic_layout);
        }

        test_layout::<[u8; 3], DefaultHandle, 10>();
        test_layout::<[u8; 25], DefaultHandle, 20>();
        test_layout::<u128, DefaultHandle, 40>();
        test_layout::<crate::collections::ArenaDeque<u8>, DefaultHandle, 80>();
    }

    #[test]
    fn debug_impl() {
        let mut storage = [MaybeUninit::uninit(); 2048];
        let mut arena = Arena::from(&mut storage[..]);
        let mut pool: crate::collections::DirectArenaPool<&'static str, DefaultHandle> = arena.with_capacity(4);

        let empty = fmt!(arena, "{:?}", pool).unwrap();
        assert_eq!(
            &*empty,
            "DirectPool { len: 0, next_free_slot: 0, slots: [\
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
            "DirectPool { len: 4, next_free_slot: 4294967295, slots: [\
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
            "DirectPool { len: 2, next_free_slot: 2, slots: [\
                Vacant { generation: 2, next_free_slot: 4294967295 }, \
                Occupied { generation: 1, value: \"Second\" }, \
                Vacant { generation: 2, next_free_slot: 0 }, \
                Occupied { generation: 1, value: \"Fourth\" }\
            ] }"
        );
    }

    #[test]
    fn randomized_drain_filter() {
        use crate::test_utils::{DropCounter, Droppable};
        use rand::{rngs::SmallRng, RngCore, SeedableRng};
        let mut rng = SmallRng::from_seed(crate::test_utils::RNG_SEED);

        let drop_count = DropCounter::new();
        let mut inserted = 0;

        let mut storage = [MaybeUninit::uninit(); 2048];
        let mut arena = Arena::from(&mut storage[..]);
        let mut pool: crate::collections::DirectArenaPool<Droppable, DefaultHandle> = arena.with_capacity(32);

        for _ in 0..1000 {
            let remaining_slots = pool.capacity() - pool.len();
            let to_be_inserted = (u64::from(rng.next_u32()) * remaining_slots as u64) >> 32;
            for _ in 0..to_be_inserted {
                pool.insert(drop_count.new_droppable(()));
            }
            inserted += to_be_inserted;

            let _ret = pool.drain_filter(|_, _| rng.next_u32().count_ones() >= 16);
        }

        assert_eq!(drop_count.dropped() as u64, inserted - pool.len() as u64);

        pool.drain();
        assert_eq!(drop_count.dropped() as u64, inserted);
    }
}
