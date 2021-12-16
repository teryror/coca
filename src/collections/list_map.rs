//! A map based on an [association list](https://en.wikipedia.org/wiki/Association_list).

use core::alloc::{Layout, LayoutError};
use core::borrow::Borrow;
use core::fmt::Debug;
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem::MaybeUninit;

use crate::storage::{Capacity, LayoutSpec, Storage};

use self::Entry::*;

/// The [`LayoutSpec`] for a [`ListMap`].
pub struct ListMapLayout<K, V>(PhantomData<(K, V)>);
impl<K, V> LayoutSpec for ListMapLayout<K, V> {
    fn layout_with_capacity(items: usize) -> Result<Layout, LayoutError> {
        let keys_array = Layout::array::<K>(items)?;
        let values_array = Layout::array::<V>(items)?;
        let (extended, _) = keys_array.extend(values_array)?;
        Ok(extended.pad_to_align())
    }
}

/// A map based on an [association list](https://en.wikipedia.org/wiki/Association_list).
/// 
/// Conventionally, this refers to a linked list of key-value pairs, using a
/// linear scan to find the value associated with a given key. This is simple,
/// though inefficient, particularly on modern computer architectures, where
/// traversing each link in the list is likely to cause a cache miss.
/// 
/// For this reason, this implementation uses arrays instead, one for the keys,
/// one for the values. This way, unrelated values need not be fetched into the
/// cache during the key lookup. Nonetheless, this search is *O*(*n*), i.e. it
/// takes time linear in the number of entries, which can be problematic for
/// large maps.
/// 
/// Newly inserted entries are appended to the arrays, and a removed entry is
/// replaced by the last one in the list, meaning modifications have constant
/// overhead after the initial lookup. This also means insertion order is **not**
/// preserved.
/// 
/// As key search is the primary cost of these operations, care should be taken
/// to avoid redundant lookups. Use the [`Entry` API](ListMap::try_entry) where
/// applicable.
pub struct ListMap<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> {
    buf: S,
    len: I,
    pairs: PhantomData<(K, V)>,
}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> From<S> for ListMap<K, V, S, I> {
    fn from(buf: S) -> Self {
        ListMap { buf, len: I::from_usize(0), pairs: PhantomData }
    }
}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> ListMap<K, V, S, I> {
    /// Returns the number of entries the map can hold.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Returns a slice of all keys in the map in arbitrary order.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    /// 
    /// for key in map.keys() {
    ///     println!("{}", key);
    /// }
    /// ```
    #[inline]
    pub fn keys(&self) -> &[K] {
        let ptr = self.buf.get_ptr().cast();
        unsafe { core::slice::from_raw_parts(ptr, self.len.as_usize()) }
    }

    #[inline(always)]
    fn values_offset(&self) -> usize {
        let cap = self.capacity();
        let keys_array = Layout::array::<K>(cap).unwrap();
        let values_array = Layout::array::<V>(cap).unwrap();
        let (_, offset) = keys_array.extend(values_array).unwrap();
        offset
    }

    /// Returns a slice of all values in the map in arbitrary order.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    /// 
    /// for val in map.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    #[inline]
    pub fn values(&self) -> &[V] {
        unsafe {
            let ptr = self.buf.get_ptr().add(self.values_offset()).cast();
            core::slice::from_raw_parts(ptr, self.len())
        }
    }

    /// Returns a mutable slice of all values in the map in arbitrary order.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    /// 
    /// for val in map.values_mut() {
    ///     *val = *val * 2;
    /// }
    /// 
    /// assert_eq!(map.get("a"), Some(&2));
    /// assert_eq!(map.get("b"), Some(&4));
    /// assert_eq!(map.get("c"), Some(&6));
    /// ```
    #[inline]
    pub fn values_mut(&mut self) -> &mut [V] {
        unsafe {
            let ptr = self.buf.get_mut_ptr().add(self.values_offset()).cast();
            core::slice::from_raw_parts_mut(ptr, self.len())
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// The iterator element type is `(&'a K, &'a V)`.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    /// 
    /// for (key, val) in map.iter() {
    ///     println!("{} -> {}", key, val);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V, S, I> {
        Iter { map: self, front: I::from_usize(0) }
    }

    /// An iterator visiting all key-value pairs in arbitrary order, with
    /// mutable references to the values. The iterator element type is
    /// `(&'a K, &'a mut V)`.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    /// 
    /// for (_, val) in map.iter_mut() {
    ///     *val *= 2;
    /// }
    /// 
    /// assert_eq!(map.get("a"), Some(&2));
    /// assert_eq!(map.get("b"), Some(&4));
    /// assert_eq!(map.get("c"), Some(&6));
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V, S, I> {
        IterMut { map: self, front: I::from_usize(0) }
    }

    /// Returns the number of entries in the map.
    #[inline]
    pub fn len(&self) -> usize {
        self.len.as_usize()
    }

    /// Returns `true` if the map contains no entries, or `false` otherwise.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len.as_usize() == 0
    }

    /// Returns `true` if the map contains the maximum number of entries it can hold, or `false` otherwise.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len.as_usize() == self.buf.capacity()
    }

    /// Clears the map without taking ownership, and returns all key-value pairs as an iterator.
    /// 
    /// If the iterator is only partially consumed, or not consumed at all,
    /// all remaining key-value pairs will still be removed.
    /// 
    /// It is unspecified how many pairs will be removed if a panic occurs while
    /// dropping an element, or if the [`Drain`] value is leaked.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// 
    /// for (k, v) in map.drain().take(1) {
    ///     let a = k == "a" && v == 1;
    ///     let b = k == "b" && v == 2;
    ///     assert!(a || b);
    /// }
    /// 
    /// assert!(map.is_empty());
    /// ```
    pub fn drain(&mut self) -> Drain<'_, K, V, S, I> {
        Drain { map: self }
    }

    /// Creates an iterator which uses a closure to determine if an element should be removed.
    /// 
    /// If the closure returns `true`, the element is removed from the map and
    /// yielded. If the closure returns `false`, or panics, the element remains
    /// in the map and will not be yielded.
    /// 
    /// Note that `drain_filter` lets you mutate every value in the filter
    /// closure, regardless of whether you choose to keep or remove it.
    /// 
    /// If the iterator is only partially consumed, or not consumed at all,
    /// all remaining key-value pairs will still be subjected to the closure
    /// and removed and dropped if it returns true.
    /// 
    /// It is unspecified how many pairs will be subjected to the closure if a
    /// panic occurs in the closure, or a panic occurs while dropping an element,
    /// or if the [`DrainFilter`] value is leaked.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::{InlineListMap, InlineVec};
    /// 
    /// let mut map = InlineListMap::<u32, u32, 8>::new();
    /// (0..8).for_each(|x| { map.insert(x, x); });
    /// let drained = map.drain_filter(|k, v| { *v = *v * *v; k % 2 == 0 });
    /// 
    /// let mut evens = InlineVec::<u32, 4>::new();
    /// let mut odds = InlineVec::<u32, 4>::new();
    /// 
    /// evens.extend(drained.map(|(_x, x_squared)| x_squared));
    /// evens.sort_unstable();
    /// assert_eq!(evens, [0, 4, 16, 36]);
    /// 
    /// odds.extend(map.into_values());
    /// odds.sort_unstable();
    /// assert_eq!(odds, [1, 9, 25, 49]);
    /// ```
    pub fn drain_filter<F: FnMut(&K, &mut V) -> bool>(&mut self, pred: F) -> DrainFilter<'_, K, V, S, I, F> {
        DrainFilter { map: self, should_remove: pred, front: I::from_usize(0) }
    }

    /// Clears the map, removing all key-value pairs.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// 
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    /// map.insert("d", 4);
    /// assert!(map.is_full());
    /// 
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        unsafe {
            let keys = self.buf.get_mut_ptr().cast::<K>();
            let values = self.buf.get_mut_ptr().add(self.values_offset()).cast::<V>();

            for i in 0..self.len() {
                keys.add(i).drop_in_place();
                values.add(i).drop_in_place();
            }

            self.len = I::from_usize(0);
        }
    }

    /// Gets the given key's corresponding [`Entry`] in the map for in-place manipulation.
    /// 
    /// # Panics
    /// Panics if the map is full and does not contain the given key.
    /// See [`try_entry`](ListMap::try_entry) for a checked version that never panics.
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V, S, I>
    where
        K: Eq
    {
        self.try_entry(key).ok().expect("map is already at capacity")
    }

    /// Gets the given key's corresponding [`Entry`] in the map for in-place manipulation.
    /// 
    /// Returns [`Err(key)`] if the map is full and does not contain the given key.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut letters = InlineListMap::<char, u32, 32>::new();
    /// 
    /// for ch in "i am, therefore i'm coded".chars() {
    ///     let counter = letters.try_entry(ch).unwrap().or_insert(0);
    ///     *counter += 1;
    /// }
    /// 
    /// assert_eq!(letters.get(&'a'), Some(&1));
    /// assert_eq!(letters.get(&'e'), Some(&4));
    /// assert_eq!(letters.get(&'i'), Some(&2));
    /// assert_eq!(letters.get(&'o'), Some(&2));
    /// assert_eq!(letters.get(&'u'), None);
    /// ```
    pub fn try_entry(&mut self, key: K) -> Result<Entry<'_, K, V, S, I>, K>
    where
        K: Eq
    {
        if let Some((idx, _)) = self.lookup(&key) {
            Ok(Occupied(OccupiedEntry { key, idx, map: self, }))
        } else if self.is_full() {
            Err(key)
        } else {
            Ok(Vacant(VacantEntry { key, map: self }))
        }
    }

    #[inline(always)]
    fn lookup<Q>(&self, key: &Q) -> Option<(usize, &K)>
    where
        K: Borrow<Q> + Eq,
        Q: Eq + ?Sized,
    {
        self.keys().iter().enumerate().find(|(_, k)| (*k).borrow() == key)
    }

    /// Returns a reference to the value associated with the given key.
    /// 
    /// The key may be any borrowed form of the map's key type,
    /// but `Eq` on the borrowed form *must* match that for the key type.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("a", 1);
    /// 
    /// assert_eq!(map.get("a"), Some(&1));
    /// assert_eq!(map.get("b"), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + Eq,
        Q: Eq + ?Sized,
    {
        let (idx, _) = self.lookup(key)?;
        Some(&self.values()[idx])
    }

    /// Returns the key-value pair corresponding to the given key.
    /// 
    /// The key may be any borrowed form of the map's key type,
    /// but `Eq` on the borrowed form *must* match that for the key type.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("a", 1);
    /// 
    /// assert_eq!(map.get_key_value("a"), Some((&"a", &1)));
    /// assert_eq!(map.get_key_value("b"), None);
    /// ```
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q> + Eq,
        Q: Eq + ?Sized,
    {
        let (idx, k) = self.lookup(key)?;
        Some((k, &self.values()[idx]))
    }

    /// Returns `true` if the map contains a value for the given key, or `false` otherwise.
    /// 
    /// The key may be any borrowed form of the map's key type,
    /// but `Eq` on the borrowed form *must* match that for the key type.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("a", 1);
    /// 
    /// assert_eq!(map.contains_key("a"), true);
    /// assert_eq!(map.contains_key("b"), false);
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q> + Eq,
        Q: Eq + ?Sized,
    {
        self.lookup(key).is_some()
    }

    /// Returns a mutable reference to the value associated with the given key.
    /// 
    /// The key may be any borrowed form of the map's key type,
    /// but `Eq` on the borrowed form *must* match that for the key type.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("a", 1);
    /// 
    /// if let Some(x) = map.get_mut(&"a") {
    ///     *x = *x + 2;
    /// }
    /// 
    /// assert_eq!(map.get("a"), Some(&3));
    /// ```
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q> + Eq,
        Q: Eq + ?Sized,
    {
        let (idx, _) = self.lookup(key)?;
        Some(&mut self.values_mut()[idx])
    }

    /// Inserts a key-value pair into the map.
    /// 
    /// If the map did not have this key present, [`None`] is returned.
    /// 
    /// If the map did have this key present, the value is updated, and the
    /// old value is returned. The key is not updated though; this matters for
    /// types that can be `==` without being identical.
    /// 
    /// # Panics
    /// Panics if the map is full and the given key is not present. See
    /// [`try_insert`](ListMap::try_insert) for a checked version that never panics.
    #[inline]
    #[track_caller]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> where K: Eq {
        self.try_insert(key, value).ok().expect("map is already at capacity")
    }

    /// Inserts a key-value pair into the map.
    /// 
    /// If the map did not have this key present, `Ok(None)` is returned if the
    /// key-value pair is inserted, or [`Err((key, value))`] if the map is full.
    /// 
    /// If the map did have this key present, the value is updated, and the
    /// old value is returned. The key is not updated though; this matters for
    /// types that can be `==` without being identical.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// assert_eq!(map.try_insert("a", 37), Ok(None));
    /// assert_eq!(map.try_insert("a", 42), Ok(Some(37)));
    /// 
    /// map.insert("b", 23);
    /// map.insert("c", 19);
    /// map.insert("d", 8);
    /// assert_eq!(map.is_full(), true);
    /// assert_eq!(map.try_insert("e", 0), Err(("e", 0)));
    /// ```
    pub fn try_insert(&mut self, key: K, value: V) -> Result<Option<V>, (K, V)> where K: Eq {
        if let Some((idx, _)) = self.lookup(&key) {
            return Ok(Some(core::mem::replace(&mut self.values_mut()[idx], value)));
        } else if self.is_full() {
            return Err((key, value));
        }

        let idx = self.len();
        
        unsafe {
            let buf_ptr = self.buf.get_mut_ptr();
            
            let key_ptr = buf_ptr.cast::<K>().add(idx);
            key_ptr.write(key);
            
            let value_ptr = buf_ptr.add(self.values_offset()).cast::<V>().add(idx);
            value_ptr.write(value);
        }
        
        self.len = I::from_usize(idx + 1);
        Ok(None)
    }

    /// Removes a key from the map, returning the value associated with the key
    /// if it was previously in the map.
    /// 
    /// The key may be any borrowed form of the map's key type,
    /// but [`Eq`] on the borrowed form *must* match that for the key type.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("a", 1);
    /// 
    /// assert_eq!(map.remove("a"), Some(1));
    /// assert_eq!(map.remove("a"), None);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q> + Eq,
        Q: Eq + ?Sized,
    {
        let (idx, _) = self.lookup(key)?;
        let new_len = self.len() - 1;

        unsafe {
            let buf_ptr = self.buf.get_mut_ptr();

            let keys = buf_ptr.cast::<K>();
            keys.add(idx).drop_in_place();

            let values = buf_ptr.add(self.values_offset()).cast::<V>();
            let result = values.add(idx).read();

            if idx != new_len {
                core::ptr::copy_nonoverlapping(keys.add(new_len), keys.add(idx), 1);
                core::ptr::copy_nonoverlapping(values.add(new_len), values.add(idx), 1);
            }

            self.len = I::from_usize(new_len);
            Some(result)
        }
    }

    /// Removes a key from the map, returning the stored key and associated
    /// value if the key was previously in the map.
    /// 
    /// The key may be any borrowed form of the map's key type,
    /// but [`Eq`] on the borrowed form *must* match that for the key type.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("a", 1);
    /// 
    /// assert_eq!(map.remove_entry("a"), Some(("a", 1)));
    /// assert_eq!(map.remove_entry("a"), None);
    /// ```
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Eq,
        Q: Eq + ?Sized,
    {
        let (idx, _) = self.lookup(key)?;
        let new_len = self.len() - 1;

        unsafe {
            let buf_ptr = self.buf.get_mut_ptr();

            let keys = buf_ptr.cast::<K>();
            let k = keys.add(idx).read();

            let values = buf_ptr.add(self.values_offset()).cast::<V>();
            let v = values.add(idx).read();

            if idx != new_len {
                core::ptr::copy_nonoverlapping(keys.add(new_len), keys.add(idx), 1);
                core::ptr::copy_nonoverlapping(values.add(new_len), values.add(idx), 1);
            }

            self.len = I::from_usize(new_len);
            Some((k, v))
        }
    }

    /// Retains only the elements specified by the predicate.
    /// 
    /// In other words, remove all key-value pairs `(k, v)` such that `pred(&k, &mut v)`
    /// returns `false`. The elements are visited in arbitrary (and unspecified) order.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<u32, u32, 8>::new();
    /// (0..8).for_each(|x| { map.insert(x, x*10); });
    /// assert_eq!(map.len(), 8);
    /// 
    /// map.retain(|&k, _| k % 2 == 0);
    /// assert_eq!(map.len(), 4);
    /// ```
    pub fn retain<F: FnMut(&K, &mut V) -> bool>(&mut self, mut pred: F) {
        self.drain_filter(|k, v| !(pred)(k, v)).for_each(drop);
    }

    /// Creates a consuming iterator visiting all keys in arbitrary order.
    /// The map cannot be used after calling this. The iterator element type is `K`.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::{InlineListMap, InlineVec};
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    /// 
    /// let mut vec = InlineVec::<&'static str, 4>::new();
    /// vec.extend(map.into_keys());
    /// // The keys are visited in arbitrary order,
    /// // so they must be sorted for this test.
    /// vec.sort_unstable();
    /// assert_eq!(vec, ["a", "b", "c"]);
    /// ```
    pub fn into_keys(self) -> IntoKeys<K, V, S, I> {
        IntoKeys { base: self.into_iter() }
    }

    /// Creates a consuming iterator visiting all values in arbitrary order.
    /// The map cannot be used after calling this. The iterator element type is `K`.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::{InlineListMap, InlineVec};
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    /// 
    /// let mut vec = InlineVec::<u32, 4>::new();
    /// vec.extend(map.into_values());
    /// // The values are visited in arbitrary order,
    /// // so they must be sorted for this test.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    pub fn into_values(self) -> IntoValues<K, V, S, I> {
        IntoValues { base: self.into_iter() }
    }
}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> Drop for ListMap<K, V, S, I> {
    fn drop(&mut self) {
        self.clear()
    }
}

impl<K: Debug, V: Debug, S: Storage<ListMapLayout<K, V>>, I: Capacity> Debug for ListMap<K, V, S, I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<Q, K, V, S, I> core::ops::Index<&'_ Q> for ListMap<K, V, S, I>
where
    Q: Eq + ?Sized,
    K: Eq + Borrow<Q>,
    S: Storage<ListMapLayout<K, V>>,
    I: Capacity,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

impl<K, V, S, I> Extend<(K, V)> for ListMap<K, V, S, I>
where
    K: Eq,
    S: Storage<ListMapLayout<K, V>>,
    I: Capacity
{
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        iter.for_each(move |(k, v)| { self.insert(k, v); });
    }
}

impl<'a, K, V, S, I> Extend<(&'a K, &'a V)> for ListMap<K, V, S, I>
where
    K: Clone + Eq,
    V: Clone,
    S: Storage<ListMapLayout<K, V>>,
    I: Capacity
{
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        iter.for_each(|(k, v)| {
            self.insert(k.clone(), v.clone());
        });
    }
}

impl<K, V, S1, I1, S2, I2> PartialEq<ListMap<K, V, S2, I2>> for ListMap<K, V, S1, I1>
where
    K: Eq,
    V: PartialEq,
    S1: Storage<ListMapLayout<K, V>>,
    S2: Storage<ListMapLayout<K, V>>,
    I1: Capacity,
    I2: Capacity,
{
    /// Tests for `self` and `other` to be equal, and is used by `==`.
    /// 
    /// Note that this is *O*(1) if the two maps have different sizes,
    /// but *O*(*n*²) if they are the same size.
    fn eq(&self, other: &ListMap<K, V, S2, I2>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter().all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K: Eq, V: Eq, S: Storage<ListMapLayout<K, V>>, I: Capacity> Eq for ListMap<K, V, S, I> {}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<K, V, I: Capacity> crate::collections::AllocListMap<K, V, I> {
    /// Constructs a new, empty [`AllocListMap`](crate::collections::AllocListMap)
    /// with the specified capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::from(crate::storage::AllocStorage::with_capacity(capacity))
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<K: Clone, V: Clone, I: Capacity> Clone for crate::collections::AllocListMap<K, V, I> {
    fn clone(&self) -> Self {
        let buf = crate::storage::AllocStorage::with_capacity(self.capacity());
        let mut result = ListMap {
            buf, len: self.len, pairs: PhantomData
        };

        unsafe {
            let base_ptr = result.buf.get_mut_ptr();
            let keys_ptr = base_ptr.cast::<K>();
            let values_ptr = base_ptr.add(result.values_offset()).cast::<V>();

            for (idx, (k, v)) in self.iter().enumerate() {
                keys_ptr.add(idx).write(k.clone());
                values_ptr.add(idx).write(v.clone());
            }
        }

        result
    }
}

/// A statically-sized storage block for a [`ListMap`].
#[repr(C)]
pub struct InlineStorage<K, V, const N: usize> {
    keys: [MaybeUninit<K>; N],
    values: [MaybeUninit<V>; N],
}

unsafe impl<K, V, const N: usize> Storage<ListMapLayout<K, V>> for InlineStorage<K, V, N> {
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

impl<K, V, I: Capacity, const N: usize> ListMap<K, V, InlineStorage<K, V, N>, I> {
    /// Constructs a new, empty [`InlineListMap`](crate::collections::InlineListMap).
    pub fn new() -> Self {
        let buf = unsafe { InlineStorage {
            keys: MaybeUninit::uninit().assume_init(),
            values: MaybeUninit::uninit().assume_init(),
        }};

        Self::from(buf)
    }
}

impl<K, V, I: Capacity, const N: usize> Default for ListMap<K, V, InlineStorage<K, V, N>, I> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Clone, V: Clone, I: Capacity, const N: usize> Clone for ListMap<K, V, InlineStorage<K, V, N>, I> {
    fn clone(&self) -> Self {
        let buf = unsafe { InlineStorage {
            keys: MaybeUninit::uninit().assume_init(),
            values: MaybeUninit::uninit().assume_init(),
        }};

        let mut result = ListMap {
            buf, len: self.len, pairs: PhantomData,
        };

        unsafe {
            let base_ptr = result.buf.get_mut_ptr();
            let keys_ptr = base_ptr.cast::<K>();
            let values_ptr = base_ptr.add(result.values_offset()).cast::<V>();

            for (idx, (k, v)) in self.iter().enumerate() {
                keys_ptr.add(idx).write(k.clone());
                values_ptr.add(idx).write(v.clone());
            }
        }

        result
    }
}

/// A view into an occupied entry in a [`ListMap`]. It is part of the [`Entry`] enum.
pub struct OccupiedEntry<'a, K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> {
    key: K,
    idx: usize,
    map: &'a mut ListMap<K, V, S, I>,
}

impl<'a, K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> OccupiedEntry<'a, K, V, S, I> {
    /// Gets a reference to the key used to create the entry.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Take the ownership of the key and value from the map.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// use coca::collections::list_map::Entry;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// 
    /// map.entry("foobar").or_insert(12);
    /// assert_eq!(map.get("foobar"), Some(&12));
    /// 
    /// if let Entry::Occupied(o) = map.entry("foobar") {
    ///     o.remove_entry();
    /// }
    /// 
    /// assert_eq!(map.contains_key("foobar"), false);
    /// ```
    pub fn remove_entry(self) -> (K, V) {
        unsafe {
            let base_ptr = self.map.buf.get_mut_ptr();

            let keys_ptr = base_ptr.cast::<K>();
            let k = keys_ptr.add(self.idx).read();

            let values_ptr = base_ptr.add(self.map.values_offset()).cast::<V>();
            let v = values_ptr.add(self.idx).read();

            let new_len = self.map.len() - 1;
            if self.idx != new_len {
                core::ptr::copy_nonoverlapping(keys_ptr.add(new_len), keys_ptr.add(self.idx), 1);
                core::ptr::copy_nonoverlapping(values_ptr.add(new_len), values_ptr.add(self.idx), 1);
            }

            self.map.len = I::from_usize(new_len);
            (k , v)
        }
    }

    /// Gets a reference to the value in the entry.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// use coca::collections::list_map::Entry;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// 
    /// map.entry("foobar").or_insert(12);
    /// assert_eq!(map.get("foobar"), Some(&12));
    /// 
    /// if let Entry::Occupied(o) = map.entry("foobar") {
    ///     assert_eq!(o.get(), &12);
    /// }
    /// ```
    pub fn get(&self) -> &V {
        unsafe {
            let base_ptr = self.map.buf.get_ptr();
            let values_ptr = base_ptr.add(self.map.values_offset()).cast::<V>();
            values_ptr.add(self.idx).as_ref().unwrap()
        }
    }

    /// Gets a mutable reference to the value in the entry.
    /// 
    /// If you need a reference to the value which may outlive the `Entry`,
    /// see [`into_mut`](OccupiedEntry::into_mut).
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// use coca::collections::list_map::Entry;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// 
    /// map.entry("foobar").or_insert(12);
    /// assert_eq!(map.get("foobar"), Some(&12));
    /// 
    /// if let Entry::Occupied(mut o) = map.entry("foobar") {
    ///     *o.get_mut() += 10;
    ///     assert_eq!(*o.get(), 22);
    /// 
    ///     // You can use the same Entry multiple times:
    ///     *o.get_mut() += 2;
    /// }
    /// 
    /// assert_eq!(map.get("foobar"), Some(&24));
    /// ```
    pub fn get_mut(&mut self) -> &mut V {
        unsafe {
            let base_ptr = self.map.buf.get_mut_ptr();
            let values_ptr = base_ptr.add(self.map.values_offset()).cast::<V>();
            values_ptr.add(self.idx).as_mut().unwrap()
        }
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value
    /// in the entry with a lifetime bound to the map itself.
    /// 
    /// If you need multiple references to the `OccupiedEntry`,
    /// see [`get_mut`](OccupiedEntry::get_mut).
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// use coca::collections::list_map::Entry;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// 
    /// map.entry("foobar").or_insert(12);
    /// assert_eq!(map.get("foobar"), Some(&12));
    /// 
    /// if let Entry::Occupied(o) = map.entry("foobar") {
    ///     *o.into_mut() += 10;
    /// }
    /// 
    /// assert_eq!(map.get("foobar"), Some(&22));
    /// ```
    pub fn into_mut(self) -> &'a mut V {
        unsafe {
            let base_ptr = self.map.buf.get_mut_ptr();
            let values_ptr = base_ptr.add(self.map.values_offset()).cast::<V>();
            values_ptr.add(self.idx).as_mut().unwrap()
        }
    }

    /// Sets the value of the entry, and returns the entry's old value.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// use coca::collections::list_map::Entry;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// 
    /// map.entry("foobar").or_insert(12);
    /// assert_eq!(map.get("foobar"), Some(&12));
    /// 
    /// if let Entry::Occupied(mut o) = map.entry("foobar") {
    ///     assert_eq!(o.insert(15), 12);
    /// }
    /// 
    /// assert_eq!(map.get("foobar"), Some(&15));
    /// ```
    pub fn insert(&mut self, value: V) -> V {
        unsafe {
            let base_ptr = self.map.buf.get_mut_ptr();
            let values_ptr = base_ptr.add(self.map.values_offset()).cast::<V>();
            values_ptr.add(self.idx).replace(value)
        }
    }

    /// Takes the value out of the entry, and returns it.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// use coca::collections::list_map::Entry;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// 
    /// map.entry("foobar").or_insert(12);
    /// assert_eq!(map.get("foobar"), Some(&12));
    /// 
    /// if let Entry::Occupied(o) = map.entry("foobar") {
    ///     assert_eq!(o.remove(), 12);
    /// }
    /// 
    /// assert_eq!(map.contains_key("foobar"), false);
    /// ```
    pub fn remove(self) -> V {
        unsafe {
            let base_ptr = self.map.buf.get_mut_ptr();

            let values_ptr = base_ptr.add(self.map.values_offset()).cast::<V>();
            let value = values_ptr.add(self.idx).read();
            
            let new_len = self.map.len() - 1;
            if self.idx != new_len {
                let keys_ptr = base_ptr.cast::<K>();
                core::ptr::copy_nonoverlapping(keys_ptr.add(new_len), keys_ptr.add(self.idx), 1);
                core::ptr::copy_nonoverlapping(values_ptr.add(new_len), values_ptr.add(self.idx), 1);
            }

            self.map.len = I::from_usize(new_len);
            value
        }
    }

    /// Replaces the entry, returning the old key-value pair. The new key in the map will be the key used to create the entry.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// use coca::collections::list_map::Entry;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.insert("foobar", 15);
    /// 
    /// if let Entry::Occupied(entry) = map.entry("foobar") {
    ///     let (old_key, old_value) = entry.replace_entry(16);
    ///     
    ///     assert_eq!(old_key, "foobar");
    ///     assert_eq!(old_value, 15);
    /// }
    /// 
    /// assert_eq!(map.get("foobar"), Some(&16));
    /// ```
    pub fn replace_entry(self, value: V) -> (K, V) {
        unsafe {
            let base_ptr = self.map.buf.get_mut_ptr();

            let keys_ptr = base_ptr.cast::<K>();
            let k = keys_ptr.add(self.idx).replace(self.key);

            let values_ptr = base_ptr.add(self.map.values_offset()).cast::<V>();
            let v = values_ptr.add(self.idx).replace(value);

            (k, v)
        }
    }

    /// Replaces the key in the map with the one used to create the entry.
    /// 
    /// This matters for key types that can be `==` without being identical.
    pub fn replace_key(self) -> K {
        unsafe {
            let keys_ptr = self.map.buf.get_mut_ptr().cast::<K>();
            keys_ptr.add(self.idx).replace(self.key)
        }
    }
}

impl<K: Debug, V: Debug, S: Storage<ListMapLayout<K, V>>, I: Capacity> Debug for OccupiedEntry<'_, K, V, S, I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("key", &self.key)
            .field("value", self.get())
            .finish()
    }
}

/// A view into a vacant entry in a [`ListMap`]. It is part of the [`Entry`] enum.
pub struct VacantEntry<'a, K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> {
    key: K,
    map: &'a mut ListMap<K, V, S, I>,
}

impl<'a, K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> VacantEntry<'a, K, V, S, I> {
    /// Gets a reference to the key that would be used when inserting through the `VacantEntry`.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Take ownership of the key.
    pub fn into_key(self) -> K {
        self.key
    }

    /// Sets the value of the entry with the `VacantEntry`'s key, and returns a mutable reference to it.
    pub fn insert(self, value: V) -> &'a mut V {
        unsafe {
            let len = self.map.len();
            let base_ptr = self.map.buf.get_mut_ptr();

            let keys_ptr = base_ptr.cast::<K>();
            keys_ptr.add(len).write(self.key);

            let values_ptr = base_ptr.add(self.map.values_offset()).cast::<V>();
            let v_ptr = values_ptr.add(len);
            v_ptr.write(value);

            self.map.len = I::from_usize(len + 1);
            v_ptr.as_mut().unwrap()
        }
    }
}

impl<K: Debug, V: Debug, S: Storage<ListMapLayout<K, V>>, I: Capacity> Debug for VacantEntry<'_, K, V, S, I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("VacantEntry").field(&self.key).finish()
    }
}

/// A view into a single entry in a map, which may be either vacant or occupied.
/// 
/// This `enum` is constructed from the [`try_entry`](ListMap::try_entry) method on [`ListMap`].
pub enum Entry<'a, K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K, V, S, I>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, K, V, S, I>),
}

impl<'a, K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> Entry<'a, K, V, S, I> {
    /// Ensures a value is in the entry by inserting the `default` if empty,
    /// and returns a mutable reference to the value in the entry.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    ///
    /// map.entry("foobar").or_insert(3);
    /// assert_eq!(map.get("foobar"), Some(&3));
    /// 
    /// *map.entry("foobar").or_insert(5) *= 2;
    /// assert_eq!(map.get("foobar"), Some(&6));
    /// ```
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the `default`
    /// function if empty, and returns a mutable reference to the value in the entry.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// let bazz = 0xDEADBEEF;
    /// 
    /// map.entry("foobar").or_insert_with(|| bazz);
    /// assert_eq!(map.get("foobar"), Some(&bazz));
    /// ```
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows for generating key-derived values for insertion by providing the default
    /// function a reference to the key that was moved during the `.entry(key)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, usize, 4>::new();
    /// 
    /// map.entry("foobar").or_insert_with_key(|key| key.chars().count());
    /// 
    /// assert_eq!(map.get("foobar"), Some(&6));
    /// ```
    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => {
                let value = default(entry.key());
                entry.insert(value)
            }
        }
    }

    /// Returns a reference to the key used to create the entry.
    pub fn key(&self) -> &K {
        match *self {
            Occupied(ref entry) => entry.key(),
            Vacant(ref entry) => entry.key(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    ///
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// 
    /// map.entry("foobar")
    ///     .and_modify(|v| { *v += 1 })
    ///     .or_insert(37);
    /// assert_eq!(map.get("foobar"), Some(&37));
    /// 
    /// map.entry("foobar")
    ///     .and_modify(|v| { *v += 1 })
    ///     .or_insert(42);
    /// assert_eq!(map.get("foobar"), Some(&38));
    /// ```
    pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Self {
        match self {
            Occupied(mut entry) => {
                f(entry.get_mut());
                Occupied(entry)
            },
            Vacant(entry) => Vacant(entry),
        }
    }
}

impl<'a, K, V: Default, S: Storage<ListMapLayout<K, V>>, I: Capacity> Entry<'a, K, V, S, I> {
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListMap;
    /// 
    /// let mut map = InlineListMap::<&'static str, u32, 4>::new();
    /// map.entry("foobar").or_default();
    /// 
    /// assert_eq!(map.get("foobar"), Some(&0));
    /// ```
    pub fn or_default(self) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(V::default())
        }
    }
}

impl<K: Debug, V: Debug, S: Storage<ListMapLayout<K, V>>, I: Capacity> Debug for Entry<'_, K, V, S, I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Vacant(ref v) => f.debug_tuple("Entry").field(v).finish(),
            Occupied(ref o) => f.debug_tuple("Entry").field(o).finish(),
        }
    }
}

/// An iterator over the entries of a [`ListMap`].
/// 
/// This `struct` is created by the [`iter`](ListMap::iter) method on `ListMap`.
/// See its documentation for more.
pub struct Iter<'a, K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> {
    map: &'a ListMap<K, V, S, I>,
    front: I,
}

impl<'a, K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> Iterator for Iter<'a, K, V, S, I> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let front = self.front.as_usize();
        if front >= self.map.len() { return None; }

        let k = &self.map.keys()[front];
        let v = &self.map.values()[front];
        self.front = I::from_usize(front + 1);

        Some((k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let front = self.front.as_usize();
        let len = self.map.len() - front;
        (len, Some(len))
    }
}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> ExactSizeIterator for Iter<'_, K, V, S, I> {}
impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> FusedIterator for Iter<'_, K, V, S, I> {}

impl<'a, K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> IntoIterator for &'a ListMap<K, V, S, I> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V, S, I>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// A mutable iterator over the entries of a [`ListMap`].
/// 
/// This `struct` is created by the [`iter_mut`](ListMap::iter_mut)
/// method on `ListMap`. See its documentation for more.
pub struct IterMut<'a, K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> {
    map: &'a mut ListMap<K, V, S, I>,
    front: I,
}

impl<'a, K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> Iterator for IterMut<'a, K, V, S, I> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        let front = self.front.as_usize();
        if front >= self.map.len() { return None; }

        let (k, v) = unsafe {
            let base_ptr = self.map.buf.get_mut_ptr();
            
            let keys_ptr = base_ptr.cast::<K>();
            let k = keys_ptr.add(front).as_ref().unwrap();

            let values_ptr = base_ptr.add(self.map.values_offset()).cast::<V>();
            let v = values_ptr.add(front).as_mut().unwrap();

            (k, v)
        };

        self.front = I::from_usize(front + 1);
        Some((k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let front = self.front.as_usize();
        let len = self.map.len() - front;
        (len, Some(len))
    }
}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> ExactSizeIterator for IterMut<'_, K, V, S, I> {}
impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> FusedIterator for IterMut<'_, K, V, S, I> {}

impl<'a, K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> IntoIterator for &'a mut ListMap<K, V, S, I> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V, S, I>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// An owning iterator over the entries of a [`ListMap`].
/// 
/// This `struct` is created by the [`into_iter`](IntoIterator::into_iter)
/// method on `ListMap` (provided by the [`IntoIterator`] trait). See its
/// documentation for more.
pub struct IntoIter<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> {
    map: ListMap<K, V, S, I>,
}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> Iterator for IntoIter<K, V, S, I> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.map.len() == 0 { return None; }

        let new_len = self.map.len() - 1;
        self.map.len = I::from_usize(new_len);

        unsafe {
            let base_ptr = self.map.buf.get_ptr();
            
            let keys_ptr = base_ptr.cast::<K>();
            let k = keys_ptr.add(new_len).read();

            let values_ptr = base_ptr.add(self.map.values_offset()).cast::<V>();
            let v = values_ptr.add(new_len).read();

            Some((k, v))
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.map.len();
        (len, Some(len))
    }
}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> ExactSizeIterator for IntoIter<K, V, S, I> {}
impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> FusedIterator for IntoIter<K, V, S, I> {}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> IntoIterator for ListMap<K, V, S, I> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, S, I>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { map: self }
    }
}

/// An owning iterator over the keys of a [`ListMap`].
/// 
/// This `struct` is created by the [`into_keys`](ListMap::into_keys) method on `ListMap`.
/// See its documentation for more.
pub struct IntoKeys<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> {
    base: IntoIter<K, V, S, I>,
}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> Iterator for IntoKeys<K, V, S, I> {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        self.base.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.base.size_hint()
    }
}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> ExactSizeIterator for IntoKeys<K, V, S, I> {}
impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> FusedIterator for IntoKeys<K, V, S, I> {}

/// An owning iterator over the values of a [`ListMap`].
/// 
/// This `struct` is created by the [`into_values`](ListMap::into_values) method on `ListMap`.
/// See its documentation for more.
pub struct IntoValues<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> {
    base: IntoIter<K, V, S, I>,
}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> Iterator for IntoValues<K, V, S, I> {
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        self.base.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.base.size_hint()
    }
}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> ExactSizeIterator for IntoValues<K, V, S, I> {}
impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> FusedIterator for IntoValues<K, V, S, I> {}

/// A draining iterator over the entries of a [`ListMap`].
/// 
/// This `struct` is created by the [`drain`](ListMap::drain) method on `ListMap`.
/// See its documentation for more.
pub struct Drain<'a, K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> {
    map: &'a mut ListMap<K, V, S, I>,
}

impl<'a, K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> Iterator for Drain<'a, K, V, S, I> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        let len = self.map.len();
        if len == 0 { return None; }

        let new_len = len - 1;
        self.map.len = I::from_usize(new_len);

        unsafe {
            let base_ptr = self.map.buf.get_ptr();
            
            let keys_ptr = base_ptr.cast::<K>();
            let k = keys_ptr.add(new_len).read();

            let values_ptr = base_ptr.add(self.map.values_offset()).cast::<V>();
            let v = values_ptr.add(new_len).read();

            Some((k, v))
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.map.len();
        (len, Some(len))
    }
}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> ExactSizeIterator for Drain<'_, K, V, S, I> {}
impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> FusedIterator for Drain<'_, K, V, S, I> {}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> Drop for Drain<'_, K, V, S, I> {
    fn drop(&mut self) {
        self.for_each(drop);
    }
}

/// A draining, filtering iterator over the entries of a [`ListMap`].
/// 
/// This `struct` is created by the [`drain_filter`](ListMap::drain_filter)
/// method on `ListMap`. See its documentation for more.
pub struct DrainFilter<'a, K, V, S, I, F>
where
    S: Storage<ListMapLayout<K, V>>,
    I: Capacity,
    F: FnMut(&K, &mut V) -> bool,
{
    map: &'a mut ListMap<K, V, S, I>,
    should_remove: F,
    front: I,
}

impl<'a, K, V, S, I, F> Iterator for DrainFilter<'a, K, V, S, I, F>
where
    S: Storage<ListMapLayout<K, V>>,
    I: Capacity,
    F: FnMut(&K, &mut V) -> bool
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        let mut front = self.front.as_usize();
        while front < self.map.len() {
            unsafe {
                let base_ptr = self.map.buf.get_mut_ptr();
                let keys_ptr = base_ptr.cast::<K>();
                let values_ptr = base_ptr.add(self.map.values_offset()).cast::<V>();

                let k = keys_ptr.add(front).as_ref().unwrap();
                let v = values_ptr.add(front).as_mut().unwrap();

                if (self.should_remove)(k, v) {
                    let new_len = self.map.len() - 1;
                    self.map.len = I::from_usize(new_len);

                    let k = keys_ptr.add(front).read();
                    let v = values_ptr.add(front).read();

                    if front < new_len {
                        core::ptr::copy_nonoverlapping(keys_ptr.add(new_len), keys_ptr.add(front), 1);
                        core::ptr::copy_nonoverlapping(values_ptr.add(new_len), values_ptr.add(front), 1);
                    }

                    self.front = I::from_usize(front);
                    return Some((k, v));
                }
            }

            front += 1;
        }

        self.front = I::from_usize(front);
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let max_len = self.map.len() - self.front.as_usize();
        (0, Some(max_len))
    }
}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity, F: FnMut(&K, &mut V) -> bool> FusedIterator for DrainFilter<'_, K, V, S, I, F> {}

impl<'a, K, V, S, I, F> Drop for DrainFilter<'a, K, V, S, I, F>
where
    S: Storage<ListMapLayout<K, V>>,
    I: Capacity,
    F: FnMut(&K, &mut V) -> bool
{
    fn drop(&mut self) {
        self.for_each(drop);
    }
}