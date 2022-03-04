//! Forgetful map data structures.
//! 
//! Useful for approximate search tasks and caching the results of expensive
//! computations.

#![allow(clippy::cast_possible_truncation)]

use core::{borrow::Borrow, cell::Cell};
use core::hash::{BuildHasher, BuildHasherDefault, Hash, Hasher};
use core::marker::PhantomData;
use core::mem::MaybeUninit;

use crate::storage::{ArrayLayout, InlineStorage, Storage};

// TODO: wider cache line types!

/// Types that can be used as the cache line type `L` of a [`CacheTable`].
pub trait CacheLine<K: Eq, V> {
    /// The maximum number of entries that can be cached in a line.
    const CAPACITY: usize;
    /// Initialize the pointed to cache line to be empty.
    /// 
    /// # Safety
    /// Implementors may assume the provided pointer to be valid and non-null;
    /// they may *not* assume the referenced memory to be initialized.
    unsafe fn init(this: *mut Self);
    /// Returns a reference to the value corresponding to the key.
    /// 
    /// The key may be any borrowed form of the cache's key type, but [`Eq`] on
    /// the borrowed form *must* match that of the key type.
    fn get<Q: Borrow<K>>(&self, k: &Q) -> Option<&V>;
    /// Returns a mutable reference to the value corresponding to the key.
    /// 
    /// The key may be any borrowed form of the cache's key type, but [`Eq`] on
    /// the borrowed form *must* match that of the key type.
    fn get_mut<Q: Borrow<K>>(&mut self, k: &Q) -> Option<&mut V>;
    /// Inserts a key-value pair into the cache line.
    /// 
    /// If the cache line is already full, another key-value pair must be
    /// evicted from the cache line and returned. Otherwise returns [`None`].
    fn insert(&mut self, k: K, v: V) -> Option<(K, V)>;
    /// Ensures a value corresponding to the provided key is cached by inserting
    /// the result of the default function if none is found, and returns a reference
    /// to the cached value.
    fn get_or_insert_with<F: FnOnce(&K) -> V>(&mut self, k: K, default: F) -> &V;
    /// Clears the cache line, removing all key-value pairs and resetting any
    /// additional state.
    fn clear(&mut self);
}

/// The smallest possible cache, storing only the single most recently accessed key-value pair.
/// 
/// Intended primarily for use as the [`CacheLine`] type `L` of a [`CacheTable`].
/// 
/// # Examples
/// ```
/// use coca::collections::cache::{UnitCache, CacheLine};
/// let mut cache = UnitCache::<&'static str, i32>::default();
/// 
/// assert!(cache.get(&"hello").is_none());
/// assert!(cache.insert("hello", 1).is_none());
/// assert_eq!(cache.get(&"hello"), Some(&1));
/// 
/// assert_eq!(cache.insert("world", 2), Some(("hello", 1)));
/// assert_eq!(cache.get(&"world"), Some(&2));
/// assert!(cache.get(&"hello").is_none());
/// ```
pub struct UnitCache<K, V> {
    key: MaybeUninit<K>,
    value: MaybeUninit<V>,
    occupied: bool,
}

impl<K: Eq, V> Default for UnitCache<K, V> {
    fn default() -> Self {
        let mut result = MaybeUninit::uninit();
        unsafe {
            Self::init(result.as_mut_ptr());
            result.assume_init()
        }
    }
}

impl<K: Eq, V> CacheLine<K, V> for UnitCache<K, V> {
    const CAPACITY: usize = 1;

    unsafe fn init(this: *mut Self) {
        (*this).occupied = false;
    }

    fn get<Q: Borrow<K>>(&self, k: &Q) -> Option<&V> {
        if !self.occupied { return None; }
        let my_key = unsafe { &*self.key.as_ptr() };
        if my_key == k.borrow() {
            Some(unsafe { &*self.value.as_ptr() })
        } else {
            None
        }
    }

    fn get_mut<Q: Borrow<K>>(&mut self, k: &Q) -> Option<&mut V> {
        if !self.occupied { return None; }
        let my_key = unsafe { &*self.key.as_ptr() };
        if my_key == k.borrow() {
            Some(unsafe { &mut *self.value.as_mut_ptr() })
        } else {
            None
        }
    }

    fn insert(&mut self, k: K, v: V) -> Option<(K, V)> {
        let evicted = self.occupied.then(|| {
            unsafe {
                let key = self.key.as_ptr().read();
                let value = self.value.as_ptr().read();
                (key, value)
            }
        });

        self.occupied = true;
        unsafe {
            self.key.as_mut_ptr().write(k);
            self.value.as_mut_ptr().write(v);
        }

        evicted
    }

    fn get_or_insert_with<F: FnOnce(&K) -> V>(&mut self, k: K, default: F) -> &V {
        if !self.occupied {
            self.value = MaybeUninit::new(default(&k));
            self.key = MaybeUninit::new(k);
            self.occupied = true;
            return unsafe { &*self.value.as_ptr() };
        }

        if unsafe { &*self.key.as_ptr() } == &k {
            return unsafe { &*self.value.as_ptr() };
        }

        let key_ptr = self.key.as_mut_ptr();
        let value_ptr = self.value.as_mut_ptr();

        unsafe {
            value_ptr.drop_in_place();
            value_ptr.write(default(&k));

            key_ptr.drop_in_place();
            key_ptr.write(k);

            &*value_ptr
        }
    }

    fn clear(&mut self) {
        if !self.occupied {
            return;
        }

        unsafe {
            self.key.as_mut_ptr().drop_in_place();
            self.value.as_mut_ptr().drop_in_place();
        }

        self.occupied = false;
    }
}

impl<K, V> Drop for UnitCache<K, V> {
    fn drop(&mut self) {
        if !self.occupied {
            return;
        }

        unsafe {
            self.key.as_mut_ptr().drop_in_place();
            self.value.as_mut_ptr().drop_in_place();
        }
    }
}

macro_rules! get_methods {
    () => {
        fn get<Q: Borrow<K>>(&self, k: &Q) -> Option<&V> {
            for i in 0..self.len() {
                let my_key = unsafe { &*self.keys[i].as_ptr() };
                if my_key == k.borrow() {
                    self.mark_used(i);
                    return Some(unsafe { &*self.values[i].as_ptr() });
                }
            }
    
            None
        }
    
        fn get_mut<Q: Borrow<K>>(&mut self, k: &Q) -> Option<&mut V> {
            for i in 0..self.len() {
                let my_key = unsafe { &*self.keys[i].as_ptr() };
                if my_key == k.borrow() {
                    self.mark_used(i);
                    return Some(unsafe { &mut *self.values[i].as_mut_ptr() });
                }
            }
    
            None
        }
    }
}

/// A cache storing the two most recently accessed key-value pairs.
/// 
/// Intended primarily for use as the [`CacheLine`] type `L` of a [`CacheTable`].
/// 
/// # Examples
/// ```
/// use coca::collections::cache::{LruCache2, CacheLine};
/// let mut cache = LruCache2::<i32, &'static str>::default();
/// 
/// assert!(cache.get(&1).is_none());
/// assert!(cache.insert(1, "A").is_none());
/// assert_eq!(cache.get(&1), Some(&"A"));
/// 
/// assert!(cache.get(&2).is_none());
/// assert!(cache.insert(2, "B").is_none());
/// assert_eq!(cache.get(&1), Some(&"A")); // Entry 1 is now most recently used...
/// 
/// assert_eq!(cache.insert(3, "C"), Some((2, "B"))); // ...so entry 2 will be evicted first.
/// assert_eq!(cache.get(&1), Some(&"A"));
/// assert_eq!(cache.get(&3), Some(&"C"));
/// assert!(cache.get(&2).is_none());
/// ```
pub struct LruCache2<K, V> {
    keys: [MaybeUninit<K>; 2],
    values: [MaybeUninit<V>; 2],
    state: Cell<u8>,
}

impl<K: Eq, V> Default for LruCache2<K, V> {
    fn default() -> Self {
        let mut result = MaybeUninit::uninit();
        unsafe {
            Self::init(result.as_mut_ptr());
            result.assume_init()
        }
    }
}

impl<K, V> LruCache2<K, V> {
    #[inline(always)]
    fn len(&self) -> usize {
        (self.state.get() & 0b11) as usize
    }

    #[inline(always)]
    fn least_recently_used(&self) -> usize {
        1 ^ (self.state.get() >> 2) as usize
    }

    #[inline(always)]
    fn mark_used(&self, i: usize) {
        let len = self.len();
        debug_assert!(i < len);
        self.state.set(len as u8 | (i << 2) as u8);
    }
}

impl<K: Eq, V> CacheLine<K, V> for LruCache2<K, V> {
    const CAPACITY: usize = 2;

    unsafe fn init(this: *mut Self) {
        (*this).state = Cell::new(0);
    }

    get_methods!();

    fn insert(&mut self, k: K, v: V) -> Option<(K, V)> {
        let len = self.len();
        for i in 0..len {
            let my_key = unsafe { &*self.keys[i].as_ptr() };
            if my_key == k.borrow() {
                self.mark_used(i);
                
                let evicted = unsafe {(
                    self.keys[i].as_ptr().read(),
                    self.values[i].as_ptr().read()
                )};

                self.keys[i] = MaybeUninit::new(k);
                self.values[i] = MaybeUninit::new(v);

                return Some(evicted);
            }
        }

        if len < 2 {
            self.keys[len] = MaybeUninit::new(k);
            self.values[len] = MaybeUninit::new(v);
            self.state.set((len + 1) as u8 | (len << 2) as u8);
            None
        } else {
            let lru = self.least_recently_used();

            let evicted = unsafe {
                let key = self.keys[lru].as_ptr().read();
                let value = self.values[lru].as_ptr().read();
                (key, value)
            };

            self.keys[lru] = MaybeUninit::new(k);
            self.values[lru] = MaybeUninit::new(v);
            self.state.set((lru << 2) as u8 | 2);

            Some(evicted)
        }
    }

    fn get_or_insert_with<F: FnOnce(&K) -> V>(&mut self, k: K, default: F) -> &V {
        let len = self.len();
        for i in 0..len {
            let my_key = unsafe { &*self.keys[i].as_ptr() };
            if my_key == k.borrow() {
                self.mark_used(i);
                return unsafe { &*self.values[i].as_ptr() };
            }
        }

        let value = default(&k);
        if len < 2 {
            self.keys[len] = MaybeUninit::new(k);
            self.values[len] = MaybeUninit::new(value);
            self.state.set((len + 1) as u8 | (len << 2) as u8);
            unsafe { &*self.values[len].as_ptr() }
        } else {
            let lru = self.least_recently_used();
            self.mark_used(lru);

            unsafe {
                self.keys[lru].as_mut_ptr().drop_in_place();
                self.values[lru].as_mut_ptr().drop_in_place();
            }

            self.keys[lru] = MaybeUninit::new(k);
            self.values[lru] = MaybeUninit::new(value);

            unsafe { &*self.values[lru].as_ptr() }
        }
    }

    fn clear(&mut self) {
        for i in 0..self.len() {
            unsafe {
                self.keys[i].as_mut_ptr().drop_in_place();
                self.values[i].as_mut_ptr().drop_in_place();
            }
        }

        self.state.set(0);
    }
}

impl<K, V> Drop for LruCache2<K, V> {
    fn drop(&mut self) {
        for i in 0..self.len() {
            unsafe {
                self.keys[i].as_mut_ptr().drop_in_place();
                self.values[i].as_mut_ptr().drop_in_place();
            }
        }
    }
}

/// A map implemented with an array of [`CacheLine`]s indexed by the keys' [`Hash`].
/// 
/// The choice of cache line type has several implications for runtime performance,
/// memory overhead, and caching behavior:
/// 
/// * Using [`UnitCache`] requires an additional [`bool`] per cache slot for tracking
///   occupancy, and results in a direct-mapped cache.
/// * Using [`LruCache2`] results in a 2-way set-associative cache with a least
///   recently used eviction policy tracked per cache line with a single [`u8`].
/// 
/// Note that the cache's capacity is always an integer multiple of the cache line's
/// capacity.
/// 
/// For `no_std` compatibility, no default hash builder is provided, but when using
/// [`Hasher`] types implementing [`Default`], the constructors [`new`](CacheTable::new),
/// and [`with_capacity`](CacheTable::with_capacity)
/// are provided. Otherwise, use [`with_hasher`](CacheTable::with_hasher),
/// [`with_capacity_and_hasher`](CacheTable::with_capacity_and_hasher) or
/// [`Arena::try_cache_with_hasher`](crate::arena::Arena::try_cache_with_hasher).
pub struct CacheTable<K: Eq, V, S: Storage<ArrayLayout<L>>, L: CacheLine<K, V>, H> {
    buf: S,
    hash_builder: H,
    lines: PhantomData<L>,
    keys: PhantomData<K>,
    values: PhantomData<V>,
}

impl<K: Eq, V, S: Storage<ArrayLayout<L>>, L: CacheLine<K, V>, H: Default> From<S> for CacheTable<K, V, S, L, H> {
    fn from(buf: S) -> Self {
        let mut result = CacheTable {
            buf, hash_builder: H::default(), lines: PhantomData, keys: PhantomData, values: PhantomData,
        };
        result.init_cache_lines();
        result
    }
}

impl<K: Eq, V, S: Storage<ArrayLayout<L>>, L: CacheLine<K, V>, H> CacheTable<K, V, S, L, H> {
    fn init_cache_lines(&mut self) {
        let line_ptr = self.buf.get_mut_ptr().cast::<L>();
        for i in 0..self.buf.capacity() {
            unsafe { L::init(line_ptr.add(i)); }
        }
    }

    /// Returns the number of key-value pairs the cache can hold.
    #[inline(always)]
    pub fn capacity(&self) -> usize {
        self.buf.capacity() * L::CAPACITY
    }

    fn get_cache_line_for_hash(&self, hash: u64) -> &L {
        let line_index = hash as usize % self.buf.capacity();
        let line_ptr = self.buf.get_ptr().cast::<L>();
        unsafe { &*line_ptr.add(line_index) }
    }

    fn get_cache_line_for_hash_mut(&mut self, hash: u64) -> &mut L {
        let line_index = hash as usize % self.buf.capacity();
        let line_ptr = self.buf.get_mut_ptr().cast::<L>();
        unsafe { &mut *line_ptr.add(line_index) }
    }

    /// Clears the cache, removing all key-value pairs.
    /// 
    /// # Examples
    /// ```
    /// # extern crate rustc_hash;
    /// use rustc_hash::FxHasher;
    /// use coca::collections::InlineDirectMappedCache;
    /// use core::hash::BuildHasherDefault;
    /// 
    /// let mut cache = InlineDirectMappedCache::<i32, &'static str, BuildHasherDefault<FxHasher>, 4>::new();
    /// cache.insert(1, "A");
    /// cache.clear();
    /// assert!(cache.get(&1).is_none());
    /// ```
    pub fn clear(&mut self) {
        let num_lines = self.buf.capacity();
        let line_ptr = self.buf.get_mut_ptr().cast::<L>();
        for i in 0..num_lines {
            let line = unsafe { &mut *line_ptr.add(i) };
            line.clear();
        }
    }
}

impl<K: Eq + Hash, V, S: Storage<ArrayLayout<L>>, L: CacheLine<K, V>, H: BuildHasher> CacheTable<K, V, S, L, H> {
    /// Constructs a new cache table using the specified storage and hash builder.
    pub fn from_storage_and_hasher(buf: S, hash_builder: H) -> Self {
        let mut result = CacheTable {
            buf, hash_builder, lines: PhantomData, keys: PhantomData, values: PhantomData,
        };
        result.init_cache_lines();
        result
    }

    fn make_hash(&self, val: &K) -> u64 {
        let mut state = self.hash_builder.build_hasher();
        val.hash(&mut state);
        state.finish()
    }

    /// Returns a reference to the value corresponding to the key.
    /// 
    /// The key may be any borrowed form of the map's key type, but [`Hash`]
    /// and [`Eq`] on the borrowed form *must* match those for the key type.
    /// 
    /// # Examples
    /// ```
    /// # extern crate rustc_hash;
    /// use rustc_hash::FxHasher;
    /// use coca::collections::InlineDirectMappedCache;
    /// use core::hash::BuildHasherDefault;
    /// 
    /// let mut cache = InlineDirectMappedCache::<i32, &'static str, BuildHasherDefault<FxHasher>, 4>::new();
    /// cache.insert(1, "A");
    /// assert_eq!(cache.get(&1), Some(&"A"));
    /// assert_eq!(cache.get(&2), None);
    /// ```
    pub fn get<Q: Borrow<K>>(&self, k: &Q) -> Option<&V> {
        let key = k.borrow();
        let hash = self.make_hash(key);
        let cache_line = self.get_cache_line_for_hash(hash);
        cache_line.get(key)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    /// 
    /// # Examples
    /// ```
    /// # extern crate rustc_hash;
    /// use rustc_hash::FxHasher;
    /// use coca::collections::InlineDirectMappedCache;
    /// use core::hash::BuildHasherDefault;
    /// 
    /// let mut cache = InlineDirectMappedCache::<i32, &'static str, BuildHasherDefault<FxHasher>, 4>::new();
    /// cache.insert(1, "A");
    /// if let Some(x) = cache.get_mut(&1) {
    ///     *x = "B";
    /// }
    /// assert_eq!(cache.get(&1), Some(&"B"));
    pub fn get_mut<Q: Borrow<K>>(&mut self, k: &Q) -> Option<&mut V> {
        let key = k.borrow();
        let hash = self.make_hash(key);
        let cache_line = self.get_cache_line_for_hash_mut(hash);
        cache_line.get_mut(key)
    }

    /// Inserts a value computed from `f` into the cache if the given key is
    /// not present, then returns a reference to the value in the cache.
    /// 
    /// # Examples
    /// ```
    /// # extern crate rustc_hash;
    /// use rustc_hash::FxHasher;
    /// use coca::collections::InlineDirectMappedCache;
    /// use core::hash::BuildHasherDefault;
    /// 
    /// let mut cache = InlineDirectMappedCache::<i32, &'static str, BuildHasherDefault<FxHasher>, 4>::new();
    /// cache.insert(1, "A");
    /// assert_eq!(cache.get_or_insert_with(1, |_| "B"), &"A");
    /// # assert_eq!(cache.get(&1), Some(&"A"));
    /// assert_eq!(cache.get_or_insert_with(2, |_| "B"), &"B");
    /// # assert_eq!(cache.get(&2), Some(&"B"));
    /// ```
    pub fn get_or_insert_with<F: FnOnce(&K) -> V>(&mut self, k: K, f: F) -> &V {
        let hash = self.make_hash(&k);
        let cache_line = self.get_cache_line_for_hash_mut(hash);
        cache_line.get_or_insert_with(k, f)
    }

    /// Inserts a key-value pair into the cache.
    /// 
    /// Returns the evicted key-value pair if the cache line corresponding to
    /// the key is already full, or [`None`] otherwise.
    /// 
    /// # Examples
    /// ```
    /// # extern crate rustc_hash;
    /// use rustc_hash::FxHasher;
    /// use coca::collections::InlineDirectMappedCache;
    /// use core::hash::BuildHasherDefault;
    /// 
    /// let mut cache = InlineDirectMappedCache::<i32, &'static str, BuildHasherDefault<FxHasher>, 4>::new();
    /// assert_eq!(cache.insert(37, "a"), None);
    /// assert_eq!(cache.insert(37, "b"), Some((37, "a")));
    /// ```
    pub fn insert(&mut self, k: K, v: V) -> Option<(K, V)> {
        let hash = self.make_hash(&k);
        let cache_line = self.get_cache_line_for_hash_mut(hash);
        cache_line.insert(k, v)
    }
}

impl<K: Eq, V, S: Storage<ArrayLayout<L>>, L: CacheLine<K, V>, H> Drop for CacheTable<K, V, S, L, H> {
    fn drop(&mut self) {
        self.clear();
    }
}

impl<K: Eq + Hash, V, L: CacheLine<K, V>, H: BuildHasher, const N: usize> CacheTable<K, V, InlineStorage<L, N>, L, H> {
    /// Constructs a new, empty `CacheTable` using inline storage and the specified [`BuildHasher`].
    /// 
    /// # Examples
    /// ```
    /// # extern crate rustc_hash;
    /// type HashBuilder = core::hash::BuildHasherDefault<rustc_hash::FxHasher>;
    /// type CacheTable = coca::collections::Inline2WayLruCache<u128, &'static str, HashBuilder, 32>;
    /// let mut cache = CacheTable::with_hasher(HashBuilder::default());
    /// assert_eq!(cache.capacity(), 64);
    /// ```
    pub fn with_hasher(hash_builder: H) -> Self {
        let mut result = CacheTable {
            buf: unsafe {
                MaybeUninit::uninit().assume_init()
            },
            hash_builder,
            lines: PhantomData,
            keys: PhantomData,
            values: PhantomData
        };
        result.init_cache_lines();
        result
    }
}

impl<K: Eq + Hash, V, L: CacheLine<K, V>, H: Hasher + Default, const N: usize> CacheTable<K, V, InlineStorage<L, N>, L, BuildHasherDefault<H>> {
    /// Constructs a new, empty `CacheTable` using inline storage and the default [`BuildHasherDefault`].
    /// 
    /// # Examples
    /// ```
    /// # extern crate rustc_hash;
    /// type HashBuilder = core::hash::BuildHasherDefault<rustc_hash::FxHasher>;
    /// type CacheTable = coca::collections::Inline2WayLruCache<u128, &'static str, HashBuilder, 32>;
    /// let mut cache = CacheTable::new();
    /// assert_eq!(cache.capacity(), 64);
    /// ```
    pub fn new() -> Self {
        let mut result = CacheTable {
            buf: unsafe { MaybeUninit::uninit().assume_init() },
            hash_builder: BuildHasherDefault::default(),
            lines: PhantomData,
            keys: PhantomData,
            values: PhantomData
        };
        result.init_cache_lines();
        result
    }
}

impl<K: Eq + Hash, V, L: CacheLine<K, V>, H: Hasher + Default, const N: usize> Default for CacheTable<K, V, InlineStorage<L, N>, L, BuildHasherDefault<H>> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<K: Eq + Hash, V, L: CacheLine<K, V>, H: BuildHasher> CacheTable<K, V, crate::storage::AllocStorage<ArrayLayout<L>>, L, H> {
    /// Constructs a new, empty `CacheTable` with the specified [`BuildHasher`]
    /// and heap-allocated storage of the specified capacity, rounded up to the
    /// next largest multiple of `L::CAPACITY`.
    /// 
    /// # Examples
    /// ```
    /// # extern crate rustc_hash;
    /// type HashBuilder = core::hash::BuildHasherDefault<rustc_hash::FxHasher>;
    /// type CacheTable = coca::collections::Alloc2WayLruCache<u128, &'static str, HashBuilder>;
    /// let mut cache = CacheTable::with_capacity_and_hasher(63, HashBuilder::default());
    /// assert_eq!(cache.capacity(), 64);
    /// ```
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: H) -> Self {
        let capacity = (capacity + L::CAPACITY - 1) / L::CAPACITY;
        let buf = crate::storage::AllocStorage::with_capacity(capacity);
        Self::from_storage_and_hasher(buf, hash_builder)
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<K: Eq + Hash, V, L: CacheLine<K, V>, H: Hasher + Default> CacheTable<K, V, crate::storage::AllocStorage<ArrayLayout<L>>, L, BuildHasherDefault<H>> {
    /// Constructs a new, empty `CacheTable` with the default [`BuildHasherDefault`]
    /// and heap-allocated storage the specified capacity, rounded up to the next
    /// largest multiple of `L::CAPACITY`.
    /// 
    /// # Examples
    /// ```
    /// # extern crate rustc_hash;
    /// type HashBuilder = core::hash::BuildHasherDefault<rustc_hash::FxHasher>;
    /// type CacheTable = coca::collections::Alloc2WayLruCache<u128, &'static str, HashBuilder>;
    /// let mut cache = CacheTable::with_capacity(63);
    /// assert_eq!(cache.capacity(), 64);
    /// ```
    pub fn with_capacity(capacity: usize, ) -> Self {
        let capacity = (capacity + L::CAPACITY - 1) / L::CAPACITY;
        let buf = crate::storage::AllocStorage::with_capacity(capacity);
        let hash_builder = BuildHasherDefault::default();
        Self::from_storage_and_hasher(buf, hash_builder)
    }
}