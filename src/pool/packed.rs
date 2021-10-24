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
    /// ```
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
/// ```
/// todo!();
/// ```
pub type PackedInlinePool<T, const N: usize> = PackedPool<T, InlineStorage<T, DefaultHandle, N>, DefaultHandle>;

/// A densely packed pool that stores its contents inline, indexed by the specified custom [`Handle`].
/// 
/// # Examples
/// ```
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
        todo!()
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