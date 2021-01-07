//! Object pools with direct indexing using stable handles.
//!
//! Values are stored in an incontiguously populated array. This optimizes for
//! random access at the cost of iteration speed.

use core::alloc::{Layout, LayoutError};
use core::marker::PhantomData;
use core::mem::ManuallyDrop;

use super::Handle;
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
/// See the [super module documentation](crate::pool) for information on
/// pool-based memory management, and [this module's documentation](crate::pool::direct)
/// for details on this variation of it.
pub struct DirectPool<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> {
    buf: S,
    len: H::Index,
    next_free_slot: H::Index,
    items: PhantomData<T>,
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> From<S> for DirectPool<T, S, H> {
    fn from(buf: S) -> Self {
        // TODO: validate buf.capacity
        let cap = buf.capacity();

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
        unsafe { (*ptr).next_free_slot = sentinel };

        // initialize generation counters:
        unsafe { core::ptr::write_bytes(result.gen_counts_mut(), 0x00, cap) };

        result
    }
}

impl<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle> DirectPool<T, S, H> {
    const FREE_LIST_SENTINEL: usize = H::Index::MAX_REPRESENTABLE;

    #[inline]
    fn slots(&self) -> *const Slot<T, H::Index> {
        self.buf.get_ptr() as _
    }

    #[inline]
    fn gen_counts(&self) -> *const u32 {
        let cap = self.buf.capacity();
        let item_array = Layout::array::<Slot<T, H::Index>>(cap).unwrap();
        let gen_count_array = Layout::array::<u32>(cap).unwrap();
        let (_, offset) = item_array.extend(gen_count_array).unwrap();
        unsafe { self.buf.get_ptr().add(offset) as _ }
    }

    #[inline]
    fn slots_mut(&mut self) -> *mut Slot<T, H::Index> {
        self.buf.get_mut_ptr() as _
    }

    #[inline]
    fn gen_counts_mut(&mut self) -> *mut u32 {
        let cap = self.buf.capacity();
        let item_array = Layout::array::<Slot<T, H::Index>>(cap).unwrap();
        let gen_count_array = Layout::array::<u32>(cap).unwrap();
        let (_, offset) = item_array.extend(gen_count_array).unwrap();
        unsafe { self.buf.get_mut_ptr().add(offset) as _ }
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
    /// todo!()
    /// ```
    pub fn contains_handle(&self, handle: H) -> bool {
        let (index, input_gen_count) = handle.into_raw_parts();
        if index > self.buf.capacity() {
            return false;
        }
        let current_gen_count = unsafe { self.gen_counts().add(index).read() };
        current_gen_count == input_gen_count
    }

    /// Inserts a value into the pool, returning a unique handle to access it.
    ///
    /// Returns `Err(value)` if the pool is already at capacity.
    ///
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    pub fn try_insert(&mut self, value: T) -> Result<H, T> {
        let insert_position = self.next_free_slot.as_usize();
        if insert_position == Self::FREE_LIST_SENTINEL {
            return Err(value);
        }

        self.len = H::Index::from_usize(self.len() + 1);
        unsafe {
            let gen_count_ptr = self.gen_counts_mut().add(insert_position);
            let gen_count = gen_count_ptr.read().wrapping_add(1);
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

    /// Removes the value referred to by the specified handle from the pool,
    /// returning it unless the handle is invalid. This invalidates the handle.
    ///
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    pub fn remove(&mut self, handle: H) -> Option<T> {
        let (index, input_gen_count) = handle.into_raw_parts();
        if index > self.buf.capacity() {
            return None;
        }

        let gen_count_ptr = unsafe { self.gen_counts_mut().add(index) };
        let current_gen_count = unsafe { *gen_count_ptr };
        if current_gen_count != input_gen_count {
            return None;
        }

        let item = unsafe {
            *gen_count_ptr = current_gen_count.wrapping_add(1);

            let slot_ptr = self.slots_mut().add(index);
            let item = slot_ptr.read().item;
            (*slot_ptr).next_free_slot = self.next_free_slot;

            item
        };
        self.next_free_slot = H::Index::from_usize(index);
        Some(ManuallyDrop::into_inner(item))
    }
}