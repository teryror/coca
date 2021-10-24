//! Densely packed object pools with indirect indexing using stable handles.
//!
//! Values are packed into a contiguously populated array, which optimizes for
//! iteration speed. For random accesses, the physical array position has to be
//! looked up in a separate, incontiguously populated table.

use core::alloc::{Layout, LayoutError};
use core::marker::PhantomData;

use super::{buffer_too_large_for_handle_type, DefaultHandle, Handle};
use crate::storage::{ArenaStorage, Capacity, LayoutSpec, Storage};

/// The [`LayoutSpec`] for a [`PackedPool`].
pub struct PackedPoolLayout<T, H>(PhantomData<(T, H)>);
impl<T, H: Handle> LayoutSpec for PackedPoolLayout<T, H> {
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
/// See the [super module documentation](crate::pool) for information on
/// pool-based memory management, and [this module's documentation](crate::pool::packed)
/// for details on this variation of it.
pub struct PackedPool<T, S: Storage<PackedPoolLayout<T, H>>, H: Handle = DefaultHandle> {
    buf: S,
    len: H::Index,
    next_free_slot: H::Index,
    items: PhantomData<T>,
}

/// A densely packed pool that stores its contents in a arena-allocated memory block.
/// 
/// See [`Arena::try_packed_pool`](crate::arena::Arena::try_packed_pool) for example usage.
pub type PackedArenaPool<'src, T, H> = PackedPool<T, ArenaStorage<'src, PackedPoolLayout<T, H>>, H>;

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
        unsafe { *ptr = sentinel; }

        // initialize generation counters:
        unsafe { core::ptr::write_bytes(result.counters_mut(), 0x00, cap); }

        result
    }
}

impl<T, S: Storage<PackedPoolLayout<T, H>>, H: Handle> PackedPool<T, S, H> {
    const FREE_LIST_SENTINEL: usize = H::Index::MAX_REPRESENTABLE;

    #[inline]
    fn values(&self) -> *const T {
        self.buf.get_ptr().cast()
    }

    #[inline]
    fn values_mut(&mut self) -> *mut T {
        self.buf.get_mut_ptr().cast()
    }

    #[inline]
    fn handles(&self) -> *const H {
        let cap = self.buf.capacity();
        let values_array = Layout::array::<T>(cap).unwrap();
        let handles_array = Layout::array::<H>(cap).unwrap();
        let (_, offset) = values_array.extend(handles_array).unwrap();
        
        let base_ptr = self.buf.get_ptr();
        unsafe { base_ptr.add(offset) }.cast()
    }

    #[inline]
    fn handles_mut(&mut self) -> *mut H {
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

    /// Returns [`true`] if the specified handle is valid for this pool.
    /// 
    /// # Examples
    /// ```ignore
    /// todo!();
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
            self.next_free_slot_or_packed_index_array().add(index).read()
        };
        unsafe { self.values().add(packed_index.as_usize()).as_ref() }
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
            self.next_free_slot_or_packed_index_array().add(index).read()
        };
        unsafe { self.values_mut().add(packed_index.as_usize()).as_mut() }
    }

    /// Returns mutable references to the values corresponding to the specified
    /// handles.
    /// 
    /// Returns [`None`] if any of the handles are invalid, or if any two of
    /// them are equal to each other.
    /// 
    /// # Examples
    /// ```
    /// # use coca::pool::packed::PackedInlinePool;
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
        for i in 1..N {
            for j in 0..i {
                if handles[i] == handles[j] {
                    return None;
                }
            }
        }

        let values = self.values_mut();
        let counters = self.counters();
        let slots = self.next_free_slot_or_packed_index_array();

        let mut result: core::mem::MaybeUninit<[&mut T; N]> = core::mem::MaybeUninit::uninit();
        let result_ptr = result.as_mut_ptr().cast::<&mut T>();

        for (i, handle) in handles.iter().enumerate() {
            let (index, input_gen_count) = handle.into_raw_parts();
            if index >= self.capacity() {
                return None;
            }

            let current_gen_count = unsafe { counters.add(index).read() };
            if current_gen_count != input_gen_count || input_gen_count % 2 == 0 {
                return None;
            }

            let packed_index = unsafe { slots.add(index).read() };
            unsafe {
                let item = values.add(packed_index.as_usize()).as_mut().unwrap();
                result_ptr.add(i).write(item);
            }
        }

        Some(unsafe { result.assume_init() })
    }

    /// Inserts a value into the pool, returning a unique handle to access it.
    /// 
    /// Returns `Err(value)` if the pool is already at capacity.
    /// 
    /// # Examples
    /// ```
    /// # use coca::pool::packed::PackedInlinePool;
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

            let slot_ptr = self.next_free_slot_or_packed_index_array_mut().add(insert_position);
            self.next_free_slot = slot_ptr.read();
            slot_ptr.write(packed_insert_position);

            let handle = H::new(insert_position, gen_count);
            self.handles_mut().add(packed_insert_position.as_usize()).write(handle);
            self.values_mut().add(packed_insert_position.as_usize()).write(value);
            
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
    /// # use coca::pool::{DefaultHandle, packed::PackedInlinePool};
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

            let slot_ptr = self.next_free_slot_or_packed_index_array_mut().add(insert_position);
            self.next_free_slot = slot_ptr.read();
            slot_ptr.write(packed_insert_position);

            let handle = H::new(insert_position, gen_count);
            self.handles_mut().add(packed_insert_position.as_usize()).write(handle);
            self.values_mut().add(packed_insert_position.as_usize()).write(f(handle));
            
            Some(handle)
        }
    }

    /// Inserts a value given by `f` into the pool. The handle where the value
    /// will be stored is passed into `f`. This is useful for storing values
    /// containing their own handle.
    ///
    /// # Panics
    /// Panics if the pool is already full. See
    /// [`try_insert_with_handle`](Packed::try_insert_with_handle) for a
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
    /// # use coca::pool::packed::PackedInlinePool;
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

            let hole = self.values_mut().add(packed_index.as_usize());
            let result = hole.read();

            let new_len = self.len() - 1;
            if new_len > 0 {
                let last = self.values().add(new_len);
                core::ptr::copy(last, hole, 1);

                let hole = self.handles_mut().add(packed_index.as_usize());
                let last = self.handles().add(new_len);
                core::ptr::copy(last, hole, 1);

                let (index, _) = last.read().into_raw_parts();
                self.next_free_slot_or_packed_index_array_mut().add(index).write(packed_index);
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
    /// ```ignore
    /// todo!();
    /// ```
    pub fn retain<F: FnMut(H, &mut T) -> bool>(&mut self, mut f: F) {
        todo!()
    }

    /// Clears the pool, dropping all values. This invalidates all handles.
    /// 
    /// # Examples
    /// ```
    /// # use coca::pool::{DefaultHandle, packed::PackedInlinePool};
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
                self.values_mut().add(packed_index).drop_in_place();

                let (index, _) = self.handles().add(packed_index).read().into_raw_parts();
                *self.counters_mut().add(index) += 1;

                let slot_ptr = self.next_free_slot_or_packed_index_array_mut().add(index);
                *slot_ptr = self.next_free_slot;
                self.next_free_slot = H::Index::from_usize(index);
            }
        }

        self.len = H::Index::from_usize(0);
    }
}

impl<T, S: Storage<PackedPoolLayout<T, H>>, H: Handle> Drop for PackedPool<T, S, H> {
    fn drop(&mut self) {
        self.clear();
    }
}

/// A densely packed pool that stores its contents in globally allocated memory.
/// 
/// # Examples
/// ```ignore
/// todo!();
/// ```
#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub type PackedAllocPool<T, H = DefaultHandle> = PackedPool<T, crate::storage::AllocStorage<PackedPoolLayout<T, H>>, H>;

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<T, H: Handle> PackedAllocPool<T, H> {
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
impl<T: Clone, H: Handle> Clone for PackedAllocPool<T, H> {
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
                let src = self.values().add(i).as_ref().unwrap();
                let dst = result.values_mut().add(i);
                dst.write(src.clone())
            }
        }

        let src_handles = self.handles();
        let dst_handles = result.handles_mut();
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
    values: core::mem::MaybeUninit<[T; N]>,
    handles: core::mem::MaybeUninit<[H; N]>,
    // indices for random access:
    counters: core::mem::MaybeUninit<[u32; N]>,
    next_free_slot_or_packed_index: core::mem::MaybeUninit<[H::Index; N]>,
}

unsafe impl<T, H: Handle, const N: usize> Storage<PackedPoolLayout<T, H>> for InlineStorage<T, H, N> {
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

/// A densely packed pool that stores its contents inline, indexed by [`DefaultHandle`].
/// 
/// # Examples
/// ```ignore
/// todo!();
/// ```
pub type PackedInlinePool<T, const N: usize> = PackedPool<T, InlineStorage<T, DefaultHandle, N>, DefaultHandle>;

/// A densely packed pool that stores its contents inline, indexed by the specified custom [`Handle`].
/// 
/// # Examples
/// ```ignore
/// todo!();
/// ```
pub type TiPackedInlinePool<T, H, const N: usize> = PackedPool<T, InlineStorage<T, H, N>, H>;


impl<T, H: Handle, const N: usize> PackedPool<T, InlineStorage<T, H, N>, H> {
    /// Constructs a new, empty `DirectPool` backed by [`InlineStorage`].
    pub fn new() -> Self {
        if N >= H::MAX_INDEX {
            buffer_too_large_for_handle_type::<H>();
        }

        Self::from(InlineStorage {
            values: core::mem::MaybeUninit::uninit(),
            handles: core::mem::MaybeUninit::uninit(),
            counters: core::mem::MaybeUninit::uninit(),
            next_free_slot_or_packed_index: core::mem::MaybeUninit::uninit(),
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
                values: core::mem::MaybeUninit::uninit(),
                handles: core::mem::MaybeUninit::uninit(),
                counters: core::mem::MaybeUninit::uninit(),
                next_free_slot_or_packed_index: core::mem::MaybeUninit::uninit(),
            },
            len: self.len,
            next_free_slot: self.next_free_slot,
            items: PhantomData,
        };

        for i in 0..self.len() {
            unsafe {
                let src = self.values().add(i).as_ref().unwrap();
                let dst = result.values_mut().add(i);
                dst.write(src.clone())
            }
        }

        let src_handles = self.handles();
        let dst_handles = result.handles_mut();
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
    use crate::pool::{DefaultHandle, Handle};
    use crate::storage::LayoutSpec;

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
        test_layout::<crate::ArenaDeque<u8>, DefaultHandle, 80>();
    }
}