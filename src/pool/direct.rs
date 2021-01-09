//! Object pools with direct indexing using stable handles.
//!
//! Values are stored in an incontiguously populated array. This optimizes for
//! random access at the cost of iteration speed.

// TODO:
// - custom handle types (32 or 64 bits, variable number of bits reserved for the index)
//   - implement capacity validation
//   - review all &mut self methods for correctness
// - iterators: values, values_mut, handles, iter, iter_mut, into_iter, drain
// - non-trivial tests

use core::alloc::{Layout, LayoutError};
use core::fmt::{Debug, Formatter};
use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ops::{Index, IndexMut};

use super::{DefaultHandle, Handle};
use crate::storage::{
    buffer_too_large_for_index_type, ArenaStorage, Capacity, LayoutSpec, Storage,
};

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
pub struct DirectPool<T, S: Storage<DirectPoolLayout<T, H>>, H: Handle = DefaultHandle> {
    buf: S,
    len: H::Index,
    next_free_slot: H::Index,
    items: PhantomData<T>,
}

/// A direct-mapped pool that stores its contents in an arena-allocated memory block.
///
/// See [`Arena::try_direct_pool`](crate::Arena::try_direct_pool) for example usage.
pub type DirectArenaPool<'src, T, H = DefaultHandle> =
    DirectPool<T, ArenaStorage<'src, DirectPoolLayout<T, H>>, H>;

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
    /// # use coca::pool::{DefaultHandle, direct::DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::Arena::from(&mut backing[..]);
    /// let mut pool = arena.direct_pool::<u128, DefaultHandle>(8);
    /// let h = pool.insert(0xDEAD_BEEF);
    /// assert!(pool.contains(h));
    /// pool.remove(h);
    /// assert!(!pool.contains(h));
    /// ```
    pub fn contains(&self, handle: H) -> bool {
        let (index, input_gen_count) = handle.into_raw_parts();
        if index > self.buf.capacity() {
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
        if index > self.buf.capacity() {
            return None;
        }
        let current_gen_count = unsafe { self.gen_counts().add(index).read() };
        if current_gen_count != input_gen_count || input_gen_count % 2 == 0 {
            return None;
        }
        unsafe { (self.slots().add(index) as *const T).as_ref() }
    }

    /// Returns a mutable reference to the value corresponding to the handle.
    ///
    /// Returns [`None`] if the handle is invalid for this pool.
    pub fn get_mut(&mut self, handle: H) -> Option<&mut T> {
        let (index, input_gen_count) = handle.into_raw_parts();
        if index > self.buf.capacity() {
            return None;
        }
        let current_gen_count = unsafe { self.gen_counts().add(index).read() };
        if current_gen_count != input_gen_count || input_gen_count % 2 == 0 {
            return None;
        }
        unsafe { (self.slots_mut().add(index) as *mut T).as_mut() }
    }

    /// Inserts a value into the pool, returning a unique handle to access it.
    ///
    /// Returns `Err(value)` if the pool is already at capacity.
    ///
    /// # Examples
    /// ```
    /// # use coca::pool::{DefaultHandle, direct::DirectArenaPool};
    /// # fn test() -> Result<(), u128> {
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::Arena::from(&mut backing[..]);
    /// let mut pool = arena.direct_pool::<u128, DefaultHandle>(8);
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

    /// Inserts a value given by `f` into the pool. The handle where the value
    /// will be stored is passed into `f`. This is useful for storing values
    /// containing their own handle.
    ///
    /// Returns [`None`] if the pool is already full, without calling `f`.
    ///
    /// # Examples
    /// ```
    /// # use coca::pool::{DefaultHandle, direct::DirectArenaPool};
    /// # fn test() -> Option<()> {
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::Arena::from(&mut backing[..]);
    /// let mut pool = arena.direct_pool::<(DefaultHandle, u64), DefaultHandle>(10);
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
            let gen_count = gen_count_ptr.read().wrapping_add(1);
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
    /// # use coca::pool::{DefaultHandle, direct::DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::Arena::from(&mut backing[..]);
    /// let mut pool = arena.direct_pool::<u128, DefaultHandle>(8);
    /// let h = pool.insert(42);
    /// assert_eq!(pool.remove(h), Some(42));
    /// assert_eq!(pool.remove(h), None);
    /// ```
    pub fn remove(&mut self, handle: H) -> Option<T> {
        let (index, input_gen_count) = handle.into_raw_parts();
        if index > self.buf.capacity() || input_gen_count % 2 == 0 {
            return None;
        }

        let gen_count_ptr = unsafe { self.gen_counts_mut().add(index) };
        let current_gen_count = unsafe { *gen_count_ptr };
        if current_gen_count != input_gen_count {
            return None;
        }

        self.len = H::Index::from_usize(self.len() - 1);
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
    /// # use coca::pool::{DefaultHandle, direct::DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::Arena::from(&mut backing[..]);
    /// let mut pool = arena.direct_pool::<u128, DefaultHandle>(4);
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
        let mut num_to_check = self.len();
        let mut new_len = num_to_check;
        let slots = self.slots_mut();
        let counts = self.gen_counts_mut();
        for i in 0..self.capacity() {
            unsafe {
                let gen_count_ptr = counts.add(i);
                let gen_count = gen_count_ptr.read();

                if gen_count % 2 == 1 {
                    let h = H::new(i, gen_count);
                    let slot_ptr = slots.add(i);
                    let item = (slot_ptr as *mut T).as_mut().unwrap();

                    if !f(h, item) {
                        ManuallyDrop::drop((slot_ptr as *mut ManuallyDrop<T>).as_mut().unwrap());
                        (*slot_ptr).next_free_slot = self.next_free_slot;
                        self.next_free_slot = H::Index::from_usize(i);
                        gen_count_ptr.write(gen_count.wrapping_add(1));

                        new_len -= 1;
                    }

                    num_to_check -= 1;
                    if num_to_check == 0 {
                        break;
                    }
                }
            }
        }
        self.len = H::Index::from_usize(new_len);
    }

    /// Clears the pool, dropping all values. This invalidates all handles.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    /// ```
    /// # use coca::pool::{DefaultHandle, direct::DirectArenaPool};
    /// # let mut backing = [core::mem::MaybeUninit::uninit(); 1024];
    /// # let mut arena = coca::Arena::from(&mut backing[..]);
    /// let mut pool = arena.direct_pool::<u128, DefaultHandle>(5);
    /// for i in 0..5 {
    ///     pool.insert(i);
    /// }
    ///
    /// assert!(pool.is_full());
    /// pool.clear();
    /// assert!(pool.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.retain(|_, _| false);
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
                    ManuallyDrop::drop((item_ptr.add(i) as *mut ManuallyDrop<T>).as_mut().unwrap());
                    num_to_drop -= 1;
                }
            }
            if num_to_drop == 0 {
                break;
            }
        }
    }
}

#[derive(Debug)]
enum DebugEntry<'a, T: Debug, H: Handle> {
    Occupied {
        generation: u32,
        value: &'a T,
    },
    Vacant {
        generation: u32,
        next_free_slot: H::Index,
    },
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
                        let value = (slot_ptr.add(i) as *const T).as_ref().unwrap();
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

/// A direct-mapped pool that stores its content in globally allocated memory.
///
/// # Examples
/// ```
/// # use coca::pool::direct::DirectAllocPool;
/// let mut pool = DirectAllocPool::<u128>::with_capacity(4);
/// assert_eq!(pool.capacity(), 4);
///
/// pool.insert(1);
/// pool.insert(2);
/// pool.insert(3);
/// pool.insert(4);
/// assert_eq!(pool.try_insert(5), Err(5));
/// ```
#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub type DirectAllocPool<T, H = DefaultHandle> =
    DirectPool<T, crate::storage::AllocStorage<DirectPoolLayout<T, H>>, H>;

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<T, H: Handle> DirectAllocPool<T, H> {
    /// Constructs a new, empty [`DirectAllocPool`] with the specified capacity.
    pub fn with_capacity(capacity: H::Index) -> Self {
        let cap = capacity.as_usize();
        if capacity != H::Index::from_usize(cap) {
            buffer_too_large_for_index_type::<H::Index>();
        }

        // TODO: validate cap for irregular count/index splits (not yet implemented)
        let storage = crate::storage::AllocStorage::with_capacity(cap);
        Self::from(storage)
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<T: Clone, H: Handle> Clone for DirectAllocPool<T, H> {
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
                    let item = (src_slots.add(i) as *const T).as_ref().unwrap();
                    (dst_slots.add(i) as *mut T).write(item.clone());
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
#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
#[repr(C)]
pub struct InlineStorage<T, H: Handle, const N: usize> {
    slots: core::mem::MaybeUninit<[Slot<T, H::Index>; N]>,
    counters: core::mem::MaybeUninit<[u32; N]>,
}

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
unsafe impl<T, H: Handle, const N: usize> Storage<DirectPoolLayout<T, H>>
    for InlineStorage<T, H, N>
{
    #[inline]
    fn get_ptr(&self) -> *const u8 {
        self as *const Self as _
    }

    #[inline]
    fn get_mut_ptr(&mut self) -> *mut u8 {
        self as *mut Self as _
    }

    #[inline]
    fn capacity(&self) -> usize {
        N
    }
}

/// A direct-mapped pool that stores its contents in an inline array.
///
/// # Examples
/// ```
/// # use coca::pool::DefaultHandle;
/// # use coca::pool::direct::DirectInlinePool;
/// const A: u128 = 0x0123_4567_89AB_CDEF_0123_4567_89AB_CDEF;
/// const B: u128 = 0xFEDC_BA98_7654_3210_FEDC_BA98_7654_3210;
///
/// let mut pool = DirectInlinePool::<u128, DefaultHandle, 8>::new();
/// let a = pool.insert(A);
/// let b = pool.insert(B);
/// assert_eq!(pool.len(), 2);
/// assert_eq!(pool.remove(a), Some(A));
/// assert_eq!(pool.remove(b), Some(B));
/// assert!(pool.is_empty());
/// ```
#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
pub type DirectInlinePool<T, H, const N: usize> = DirectPool<T, InlineStorage<T, H, N>, H>;

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
impl<T, H: Handle, const N: usize> DirectInlinePool<T, H, N> {
    /// Constructs a new, empty `DirectPool` backed by [`InlineStorage`].
    pub fn new() -> Self {
        Self::from(InlineStorage {
            slots: core::mem::MaybeUninit::uninit(),
            counters: core::mem::MaybeUninit::uninit(),
        })
    }
}

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
impl<T, H: Handle, const N: usize> Default for DirectInlinePool<T, H, N> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
impl<T: Clone, H: Handle, const N: usize> Clone for DirectInlinePool<T, H, N> {
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
        unsafe { core::ptr::copy(src_counts, dst_counts, self.capacity()) };

        let src_slots = self.slots();
        let dst_slots = result.slots_mut();

        for i in 0..self.capacity() {
            unsafe {
                let generation = dst_counts.add(i).read();
                if generation % 2 == 1 {
                    let item = (src_slots.add(i) as *const T).as_ref().unwrap();
                    (dst_slots.add(i) as *mut T).write(item.clone());
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
    use crate::pool::{DefaultHandle, Handle};
    use crate::storage::LayoutSpec;
    use crate::{fmt, Arena};

    #[cfg(feature = "nightly")]
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
        test_layout::<crate::ArenaDeque<u8>, DefaultHandle, 80>();
    }

    #[test]
    fn debug_impl() {
        let mut storage = [MaybeUninit::uninit(); 2048];
        let mut arena = Arena::from(&mut storage[..]);
        let mut pool = arena.direct_pool::<&'static str, DefaultHandle>(4);

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
}
