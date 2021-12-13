pub mod binary_heap;
pub mod cache;
pub mod deque;
pub mod list_map;
pub mod option_group;
pub mod pool;
pub mod vec;

use crate::storage::{ArenaStorage, ArrayLike, InlineStorage, SliceStorage};

use binary_heap::BinaryHeap;
use cache::{CacheTable, UnitCache, LruCache2};
use deque::Deque;
use list_map::{ListMap, ListMapLayout};
use option_group::OptionGroup;
use pool::DefaultHandle;
use pool::direct::{DirectPool, DirectPoolLayout};
use pool::packed::{PackedPool, PackedPoolLayout};
use vec::Vec;

/// A binary heap using a mutable slice for storage.
///
/// # Examples
/// ```
/// use core::mem::MaybeUninit;
/// let mut backing_array = [MaybeUninit::<char>::uninit(); 32];
/// let (slice1, slice2) = (&mut backing_array[..]).split_at_mut(16);
/// let mut heap1 = coca::collections::SliceHeap::<_>::from(slice1);
/// let mut heap2 = coca::collections::SliceHeap::<_>::from(slice2);
/// assert_eq!(heap1.capacity(), 16);
/// assert_eq!(heap2.capacity(), 16);
/// ```
pub type SliceHeap<'a, T, I = usize> = BinaryHeap<T, SliceStorage<'a, T>, I>;
/// A binary heap using an arena-allocated slice for storage.
///
/// # Examples
/// ```
/// use coca::arena::Arena;
/// use coca::collections::ArenaHeap;
/// use core::mem::MaybeUninit;
///
/// let mut backing_region = [MaybeUninit::uninit(); 1024];
/// let mut arena = Arena::from(&mut backing_region[..]);
///
/// let heap: ArenaHeap<'_, i64, usize> = arena.try_with_capacity(100).unwrap();
/// assert!(arena.try_with_capacity::<_, ArenaHeap<'_, i64, usize>>(100).is_none());
/// ```
pub type ArenaHeap<'a, T, I = usize> = BinaryHeap<T, ArenaStorage<'a, ArrayLike<T>>, I>;

/// A binary heap using an inline array for storage.
///
/// # Examples
/// ```
/// let mut heap = coca::collections::InlineHeap::<char, 3>::new();
/// heap.push('a');
/// heap.push('b');
/// heap.push('c');
/// assert_eq!(heap.peek(), Some(&'c'));
/// ```
pub type InlineHeap<T, const C: usize> = BinaryHeap<T, InlineStorage<T, C>, usize>;

/// A binary heap using an inline array for storage, generic over the index type.
///
/// # Examples
/// ```
/// let mut heap = coca::collections::TiInlineHeap::<char, u8, 3>::new();
/// heap.push('a');
/// let vec = heap.into_vec();
/// assert_eq!(vec[0u8], 'a');
/// ```
pub type TiInlineHeap<T, Index, const C: usize> = BinaryHeap<T, InlineStorage<T, C>, Index>;

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
/// A binary heap using a heap-allocated slice for storage.
///
/// Note this still has a fixed capacity, and will never reallocate.
///
/// # Examples
/// ```
/// let mut heap = coca::collections::AllocHeap::<char>::with_capacity(3);
/// heap.push('a');
/// heap.push('b');
/// heap.push('c');
/// assert!(heap.try_push('d').is_err());
/// ```
pub type AllocHeap<T, I = usize> = BinaryHeap<T, crate::storage::AllocStorage<ArrayLike<T>>, I>;

/// A direct-mapped cache using an arena-allocated slice for storage.
/// 
/// # Examples
/// ```
/// # extern crate rustc_hash;
/// use rustc_hash::FxHasher;
/// use coca::{arena::Arena, collections::ArenaDirectMappedCache};
/// use core::{hash::BuildHasherDefault, mem::MaybeUninit};
/// 
/// # fn test() -> Option<()> {
/// let mut backing_region = [MaybeUninit::uninit(); 1024];
/// let mut arena = Arena::from(&mut backing_region[..]);
/// let mut cache: ArenaDirectMappedCache<'_, i32, &'static str, BuildHasherDefault<FxHasher>> = arena.try_with_capacity(8)?;
/// cache.insert(1, "a");
/// assert_eq!(cache.get(&1), Some(&"a"));
/// # Some(())
/// # }
/// # assert!(test().is_some());
/// ```
pub type ArenaDirectMappedCache<'src, K, V, H> = CacheTable<K, V, ArenaStorage<'src, ArrayLike<UnitCache<K, V>>>, UnitCache<K, V>, H>;
/// A 2-way set-associative cache with a least recently used eviction policy,
/// using an arena-allocated slice for storage.
/// 
/// # Examples
/// ```
/// # extern crate rustc_hash;
/// use rustc_hash::FxHasher;
/// use coca::{arena::Arena, collections::Arena2WayLruCache};
/// use core::{hash::BuildHasherDefault, mem::MaybeUninit};
/// 
/// # fn test() -> Option<()> {
/// let mut backing_region = [MaybeUninit::uninit(); 1024];
/// let mut arena = Arena::from(&mut backing_region[..]);
/// let mut cache: Arena2WayLruCache<'_, i32, &'static str, BuildHasherDefault<FxHasher>> = arena.try_with_capacity(8)?;
/// cache.insert(1, "a");
/// assert_eq!(cache.get(&1), Some(&"a"));
/// # Some(())
/// # }
/// # assert!(test().is_some());
/// ```
pub type Arena2WayLruCache<'src, K, V, H> = CacheTable<K, V, ArenaStorage<'src, ArrayLike<LruCache2<K, V>>>, LruCache2<K, V>, H>;

/// A direct-mapped cache using an inline array for storage.
/// 
/// # Examples
/// ```
/// # extern crate rustc_hash;
/// use rustc_hash::FxHasher;
/// # use coca::collections::InlineDirectMappedCache;
/// # use core::hash::BuildHasherDefault;
/// # fn main() {
/// let keys = ["Alice", "Bob", "Charlie", "Eve"];
/// let mut cache = InlineDirectMappedCache::<&'static str, usize, BuildHasherDefault<FxHasher>, 3>::new();
/// 
/// for k in &keys {
///     cache.insert(k, k.len());
///     assert_eq!(cache.get(k), Some(&k.len()));
/// }
/// 
/// let mut remembered = 0;
/// for k in &keys {
///     if let Some(len) = cache.get(k) {
///         assert_eq!(len, &k.len());
///         remembered += 1;
///     }
/// }
/// 
/// assert!(0 < remembered);
/// assert!(remembered < keys.len());
/// # }
/// ```
pub type InlineDirectMappedCache<K, V, H, const N: usize> = CacheTable<K, V, InlineStorage<UnitCache<K, V>, N>, UnitCache<K, V>, H>;
/// A 2-way set-associative cache with a least recently used eviction policy,
/// using an inline array for storage.
/// 
/// Note that the constant generic parameter `N` is the number of cache lines,
/// i.e. caches of this type have capacity for `2 * N` key-value pairs.
/// 
/// # Examples
/// ```
/// # extern crate rustc_hash;
/// use rustc_hash::FxHasher;
/// # use coca::collections::Inline2WayLruCache;
/// # use core::hash::BuildHasherDefault;
/// # fn main() {
/// let keys = ["Alice", "Bob", "Charlie", "David", "Eve", "Faythe", "Grace"];
/// let mut cache = Inline2WayLruCache::<&'static str, usize, BuildHasherDefault<FxHasher>, 3>::new();
/// assert_eq!(cache.capacity(), 6);
/// 
/// for k in &keys {
///     cache.insert(k, k.len());
///     assert_eq!(cache.get(k), Some(&k.len()));
/// }
/// 
/// let mut remembered = 0;
/// for k in &keys {
///     if let Some(len) = cache.get(k) {
///         assert_eq!(len, &k.len());
///         remembered += 1;
///     }
/// }
/// 
/// assert!(0 < remembered);
/// assert!(remembered < keys.len());
/// # }
/// ``` 
pub type Inline2WayLruCache<K, V, H, const N: usize> = CacheTable<K, V, InlineStorage<LruCache2<K, V>, N>, LruCache2<K, V>, H>;

/// A direct-mapped cache using a heap-allocated array for storage.
/// 
/// # Examples
/// ```
/// # extern crate rustc_hash;
/// use rustc_hash::FxHasher;
/// # use coca::collections::AllocDirectMappedCache;
/// # use core::hash::BuildHasherDefault;
/// let mut cache = AllocDirectMappedCache::<&'static str, usize, BuildHasherDefault<FxHasher>>::with_capacity(3);
/// assert_eq!(cache.capacity(), 3);
/// 
/// let keys = ["Alice", "Bob", "Charlie", "Eve"];
/// for k in &keys {
///     cache.insert(k, k.len());
///     assert_eq!(cache.get(k), Some(&k.len()));
/// }
/// 
/// let mut remembered = 0;
/// for k in &keys {
///     if let Some(len) = cache.get(k) {
///         assert_eq!(len, &k.len());
///         remembered += 1;
///     }
/// }
/// 
/// assert!(0 < remembered);
/// assert!(remembered < keys.len());
/// ```
#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub type AllocDirectMappedCache<K, V, H> = CacheTable<K, V, crate::storage::AllocStorage<ArrayLike<UnitCache<K, V>>>, UnitCache<K, V>, H>;

/// A 2-way set-associative cache with a least recently used eviction policy,
/// using a heap-allocated array for storage.
/// 
/// # Examples 
/// ```
/// # extern crate rustc_hash;
/// use rustc_hash::FxHasher;
/// # use coca::collections::Alloc2WayLruCache;
/// # use core::hash::BuildHasherDefault;
/// let mut cache = Alloc2WayLruCache::<&'static str, usize, BuildHasherDefault<FxHasher>>::with_capacity(6);
/// assert_eq!(cache.capacity(), 6);
/// 
/// let keys = ["Alice", "Bob", "Charlie", "David", "Eve", "Faythe", "Grace"];
/// for k in &keys {
///     cache.insert(k, k.len());
///     assert_eq!(cache.get(k), Some(&k.len()));
/// }
/// 
/// let mut remembered = 0;
/// for k in &keys {
///     if let Some(len) = cache.get(k) {
///         assert_eq!(len, &k.len());
///         remembered += 1;
///     }
/// }
/// 
/// assert!(0 < remembered);
/// assert!(remembered < keys.len());
/// ```
#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub type Alloc2WayLruCache<K, V, H> = CacheTable<K, V, crate::storage::AllocStorage<ArrayLike<LruCache2<K, V>>>, LruCache2<K, V>, H>;

/// A double-ended queue using any mutable slice for storage.
///
/// # Examples
/// ```
/// use core::mem::MaybeUninit;
/// let mut backing_array = [MaybeUninit::<char>::uninit(); 32];
/// let (slice1, slice2) = (&mut backing_array[..]).split_at_mut(16);
/// let mut deque1 = coca::collections::SliceDeque::<_>::from(slice1);
/// let mut deque2 = coca::collections::SliceDeque::<_>::from(slice2);
/// assert_eq!(deque1.capacity(), 16);
/// assert_eq!(deque2.capacity(), 16);
/// ```
pub type SliceDeque<'a, T, I = usize> = Deque<T, SliceStorage<'a, T>, I>;
/// A double-ended queue using an arena-allocated slice for storage.
///
/// # Examples
/// ```
/// use core::mem::MaybeUninit;
/// use coca::arena::Arena;
/// use coca::collections::ArenaDeque;
/// 
/// # fn test() -> Option<()> {
/// let mut backing_region = [MaybeUninit::uninit(); 1024];
/// let mut arena = Arena::from(&mut backing_region[..]);
/// let mut deque: ArenaDeque<'_, char, usize> = arena.try_with_capacity(4)?;
/// 
/// deque.push_front('b');
/// deque.push_front('a');
/// deque.push_back('c');
/// deque.push_back('d');
/// 
/// assert_eq!(deque, &['a', 'b', 'c', 'd']);
/// assert_eq!(deque.try_push_back('e'), Err('e'));
/// # Some(())
/// # }
/// # assert!(test().is_some());
/// ```
pub type ArenaDeque<'a, T, I = usize> = Deque<T, ArenaStorage<'a, ArrayLike<T>>, I>;

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
/// A deque using a heap-allocated slice for storage.
///
/// Note that this still has a fixed capacity, and will never reallocate.
///
/// # Examples
/// ```
/// let mut deque = coca::collections::AllocDeque::<char>::with_capacity(4);
/// 
/// deque.push_front('b');
/// deque.push_front('a');
/// deque.push_back('c');
/// deque.push_back('d');
/// 
/// assert_eq!(deque, &['a', 'b', 'c', 'd']);
/// assert_eq!(deque.try_push_back('e'), Err('e'));
/// ```
pub type AllocDeque<T, I = usize> = Deque<T, crate::storage::AllocStorage<ArrayLike<T>>, I>;

/// A deque using an inline array for storage.
///
/// # Examples
/// ```
/// let mut deque = coca::collections::InlineDeque::<char, 4>::new();
/// deque.push_front('b');
/// deque.push_front('a');
/// deque.push_back('c');
/// deque.push_back('d');
/// assert_eq!(deque, &['a', 'b', 'c', 'd']);
/// assert_eq!(deque.try_push_back('e'), Err('e'));
/// ```
pub type InlineDeque<T, const C: usize> = Deque<T, InlineStorage<T, C>, usize>;

/// A deque using an inline array for storage, generic over the index type.
///
/// # Examples
/// ```
/// let mut deque = coca::collections::TiInlineDeque::<char, u8, 4>::new();
/// deque.push_front('a');
/// assert_eq!(deque[0u8], 'a');
/// ```
pub type TiInlineDeque<T, I, const C: usize> = Deque<T, InlineStorage<T, C>, I>;

/// An association list that stores its contents in an arena-allocated memory block.
/// 
/// # Examples
/// ```
/// use coca::arena::Arena;
/// use coca::collections::ArenaListMap;
/// use core::mem::MaybeUninit;
///
/// let mut backing_region = [MaybeUninit::uninit(); 2048];
/// let mut arena = Arena::from(&mut backing_region[..]);
/// 
/// let map: ArenaListMap<'_, &'static str, u32> = arena.try_with_capacity(100).unwrap();
/// assert!(arena.try_with_capacity::<_, ArenaListMap<'_, &'static str, u32>>(100).is_none());
/// ```
pub type ArenaListMap<'a, K, V, I = usize> = ListMap<K, V, ArenaStorage<'a, ListMapLayout<K, V>>, I>;
/// An association list that stores its contents in globally allocated memory.
/// 
/// # Examples
/// ```
/// use coca::collections::AllocListMap;
/// let mut map = AllocListMap::<&'static str, u32>::with_capacity(13);
/// assert_eq!(map.capacity(), 13);
/// ```
#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub type AllocListMap<K, V, I = usize> = ListMap<K, V, crate::storage::AllocStorage<ListMapLayout<K, V>>, I>;
/// An association list that stores its contents inline.
/// 
/// # Examples
/// ```
/// use coca::collections::InlineListMap;
/// let mut map = InlineListMap::<&'static str, u32, 3>::new();
/// # assert!(map.is_empty());
/// ```
pub type InlineListMap<K, V, const N: usize> = ListMap<K, V, list_map::InlineStorage<K, V, N>, usize>;
/// An association list that stores its contents inline.
/// 
/// # Examples
/// ```
/// use coca::collections::TiInlineListMap;
/// let mut map = TiInlineListMap::<&'static str, u32, u8, 3>::new();
/// # assert!(map.is_empty());
/// ```
pub type TiInlineListMap<K, V, I, const N: usize> = ListMap<K, V, list_map::InlineStorage<K, V, N>, I>;

/// A group of up to eight [`Option`]s with the discriminants packed into a single `u8`.
pub type OptionGroup8<T> = OptionGroup<u8, T>;
/// A group of up to sixteen [`Option`]s with the discriminants packed into a single `u16`.
pub type OptionGroup16<T> = OptionGroup<u16, T>;
/// A group of up to 32 [`Option`]s with the discriminants packed into a single `u32`.
pub type OptionGroup32<T> = OptionGroup<u32, T>;
/// A group of up to 64 [`Option`]s with the discriminants packed into a single `u64`.
pub type OptionGroup64<T> = OptionGroup<u64, T>;

/// A direct-mapped pool that stores its contents in an arena-allocated memory block.
///
/// # Examples
/// ```
/// use coca::arena::Arena;
/// use coca::collections::{DirectArenaPool, pool::DefaultHandle};
/// use core::mem::MaybeUninit;
///
/// let mut backing_region = [MaybeUninit::uninit(); 1024];
/// let mut arena = Arena::from(&mut backing_region[..]);
///
/// let pool: DirectArenaPool<'_, i64, DefaultHandle> = arena.try_with_capacity(50).unwrap();
/// assert!(arena.try_with_capacity::<_, DirectArenaPool<'_, i64, DefaultHandle>>(50).is_none());
/// ```
pub type DirectArenaPool<'src, T, H = DefaultHandle> =
    DirectPool<T, ArenaStorage<'src, DirectPoolLayout<T, H>>, H>;

/// A direct-mapped pool that stores its content in globally allocated memory.
///
/// # Examples
/// ```
/// # use coca::collections::DirectAllocPool;
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

/// A direct-mapped pool that stores its contents in an inline array,
/// indexed by [`DefaultHandle`].
///
/// # Examples
/// ```
/// # use coca::collections::pool::DefaultHandle;
/// # use coca::collections::DirectInlinePool;
/// const A: u128 = 0x0123_4567_89AB_CDEF_0123_4567_89AB_CDEF;
/// const B: u128 = 0xFEDC_BA98_7654_3210_FEDC_BA98_7654_3210;
///
/// let mut pool = DirectInlinePool::<u128, 8>::new();
/// let a = pool.insert(A);
/// let b = pool.insert(B);
/// assert_eq!(pool.len(), 2);
/// assert_eq!(pool.remove(a), Some(A));
/// assert_eq!(pool.remove(b), Some(B));
/// assert!(pool.is_empty());
/// ```
pub type DirectInlinePool<T, const N: usize> = DirectPool<T, pool::direct::InlineStorage<T, DefaultHandle, N>, DefaultHandle>;

/// A direct-mapped pool that stores its contents in an inline array,
/// indexed by the specified custom [`Handle`](pool::Handle).
///
/// # Examples
/// ```
/// # use coca::handle_type;
/// # use coca::collections::TiDirectInlinePool;
/// handle_type! { CustomHandle: 8 / 32; }
/// 
/// const A: u128 = 0x0123_4567_89AB_CDEF_0123_4567_89AB_CDEF;
/// const B: u128 = 0xFEDC_BA98_7654_3210_FEDC_BA98_7654_3210;
///
/// let mut pool = TiDirectInlinePool::<u128, CustomHandle, 8>::new();
/// let a: CustomHandle = pool.insert(A);
/// let b = pool.insert(B);
/// assert_eq!(pool.len(), 2);
/// assert_eq!(pool.remove(a), Some(A));
/// assert_eq!(pool.remove(b), Some(B));
/// assert!(pool.is_empty());
/// ```
pub type TiDirectInlinePool<T, H, const N: usize> = DirectPool<T, pool::direct::InlineStorage<T, H, N>, H>;

/// A densely packed pool that stores its contents in a arena-allocated memory block.
/// 
/// # Examples
/// ```
/// use coca::arena::Arena;
/// use coca::collections::{PackedArenaPool, pool::DefaultHandle};
/// use core::mem::MaybeUninit;
///
/// let mut backing_region = [MaybeUninit::uninit(); 1024];
/// let mut arena = Arena::from(&mut backing_region[..]);
///
/// let pool: PackedArenaPool<'_, i64, DefaultHandle> = arena.try_with_capacity(30).unwrap();
/// assert!(arena.try_with_capacity::<_, PackedArenaPool<'_, i64, DefaultHandle>>(30).is_none());
/// ```
pub type PackedArenaPool<'src, T, H> = PackedPool<T, ArenaStorage<'src, PackedPoolLayout<T, H>>, H>;

/// A densely packed pool that stores its contents in globally allocated memory.
/// 
/// # Examples
/// ```
/// # use coca::collections::pool::DefaultHandle;
/// # use coca::collections::PackedAllocPool;
/// const A: u128 = 0x0123_4567_89AB_CDEF_0123_4567_89AB_CDEF;
/// const B: u128 = 0xFEDC_BA98_7654_3210_FEDC_BA98_7654_3210;
///
/// let mut pool = PackedAllocPool::<u128>::with_capacity(8);
/// let a = pool.insert(A);
/// let b = pool.insert(B);
/// assert_eq!(pool.len(), 2);
/// assert_eq!(pool.remove(a), Some(A));
/// assert_eq!(pool.remove(b), Some(B));
/// assert!(pool.is_empty());
/// ```
#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub type PackedAllocPool<T, H = DefaultHandle> = PackedPool<T, crate::storage::AllocStorage<PackedPoolLayout<T, H>>, H>;

/// A densely packed pool that stores its contents inline, indexed by [`DefaultHandle`].
/// 
/// # Examples
/// ```
/// # use coca::collections::pool::DefaultHandle;
/// # use coca::collections::PackedInlinePool;
/// const A: u128 = 0x0123_4567_89AB_CDEF_0123_4567_89AB_CDEF;
/// const B: u128 = 0xFEDC_BA98_7654_3210_FEDC_BA98_7654_3210;
///
/// let mut pool = PackedInlinePool::<u128, 8>::new();
/// let a = pool.insert(A);
/// let b = pool.insert(B);
/// assert_eq!(pool.len(), 2);
/// assert_eq!(pool.remove(a), Some(A));
/// assert_eq!(pool.remove(b), Some(B));
/// assert!(pool.is_empty());
/// ```
pub type PackedInlinePool<T, const N: usize> = PackedPool<T, pool::packed::InlineStorage<T, DefaultHandle, N>, DefaultHandle>;

/// A densely packed pool that stores its contents inline, indexed by the specified custom [`Handle`](pool::Handle).
/// 
/// # Examples
/// ```
/// # use coca::handle_type;
/// # use coca::collections::TiPackedInlinePool;
/// handle_type! { CustomHandle: 8 / 32; }
/// 
/// const A: u128 = 0x0123_4567_89AB_CDEF_0123_4567_89AB_CDEF;
/// const B: u128 = 0xFEDC_BA98_7654_3210_FEDC_BA98_7654_3210;
///
/// let mut pool = TiPackedInlinePool::<u128, CustomHandle, 8>::new();
/// let a: CustomHandle = pool.insert(A);
/// let b = pool.insert(B);
/// assert_eq!(pool.len(), 2);
/// assert_eq!(pool.remove(a), Some(A));
/// assert_eq!(pool.remove(b), Some(B));
/// assert!(pool.is_empty());
/// ```
pub type TiPackedInlinePool<T, H, const N: usize> = PackedPool<T, pool::packed::InlineStorage<T, H, N>, H>;

/// A vector using any mutable slice for storage.
///
/// # Examples
/// ```
/// use core::mem::MaybeUninit;
/// let mut backing_array = [MaybeUninit::<char>::uninit(); 32];
/// let (slice1, slice2) = (&mut backing_array[..]).split_at_mut(16);
/// let mut vec1 = coca::collections::SliceVec::<_>::from(slice1);
/// let mut vec2 = coca::collections::SliceVec::<_>::from(slice2);
/// assert_eq!(vec1.capacity(), 16);
/// assert_eq!(vec2.capacity(), 16);
/// ```
pub type SliceVec<'a, T, I = usize> = Vec<T, SliceStorage<'a, T>, I>;
/// A vector using an arena-allocated slice for storage.
///
/// # Examples
/// ```
/// use coca::arena::Arena;
/// use coca::collections::ArenaVec;
/// use core::mem::MaybeUninit;
///
/// let mut backing_region = [MaybeUninit::uninit(); 1024];
/// let mut arena = Arena::from(&mut backing_region[..]);
///
/// let v: ArenaVec<'_, i64, usize> = arena.try_with_capacity(100).unwrap();
/// assert!(arena.try_with_capacity::<_, ArenaVec<'_, i64, usize>>(100).is_none());
/// ```
pub type ArenaVec<'a, T, I = usize> = Vec<T, ArenaStorage<'a, ArrayLike<T>>, I>;

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
/// A vector using a heap-allocated slice for storage.
///
/// Note this still has a fixed capacity, and will never reallocate.
///
/// # Examples
/// ```
/// let mut vec = coca::collections::AllocVec::<char>::with_capacity(3);
/// vec.push('a');
/// vec.push('b');
/// vec.push('c');
/// assert!(vec.try_push('d').is_err());
/// ```
pub type AllocVec<T, I = usize> = Vec<T, crate::storage::AllocStorage<ArrayLike<T>>, I>;

/// A vector using an inline array for storage.
///
/// # Examples
/// ```
/// let mut vec = coca::collections::InlineVec::<char, 3>::new();
/// vec.push('a');
/// vec.push('b');
/// vec.push('c');
/// assert!(vec.try_push('d').is_err());
/// ```
pub type InlineVec<T, const C: usize> = Vec<T, InlineStorage<T, C>, usize>;

/// A vector using an inline array for storage, generic over the index type.
///
/// # Examples
/// ```
/// let mut vec = coca::collections::TiInlineVec::<char, u8, 3>::new();
/// vec.push('a');
/// assert_eq!(vec[0u8], 'a');
/// ```
pub type TiInlineVec<T, Index, const C: usize> = Vec<T, InlineStorage<T, C>, Index>;
