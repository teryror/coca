//! A map based on an [association list](https://en.wikipedia.org/wiki/Association_list).

use core::alloc::{Layout, LayoutError};
use core::borrow::Borrow;
use core::marker::PhantomData;
use core::mem::MaybeUninit;

use crate::storage::{Capacity, LayoutSpec, Storage};

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
    /// todo!()
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
    /// todo!()
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
    /// todo!()
    /// ```
    #[inline]
    pub fn values_mut(&mut self) -> &mut [V] {
        unsafe {
            let ptr = self.buf.get_mut_ptr().add(self.values_offset()).cast();
            core::slice::from_raw_parts_mut(ptr, self.len())
        }
    }

    // TODO: iter, iter_mut

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

    // TODO: drain, drain_filter

    /// Clears the map, removing all key-value pairs.
    /// 
    /// # Examples
    /// ```
    /// todo!()
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
    pub fn entry(&mut self, key: K) /* -> Entry<???> */
    where
        K: Eq
    {
        todo!()
    }

    /// Gets the given key's corresponding [`Entry`] in the map for in-place manipulation.
    /// 
    /// Returns [`Err`] if the map is full and does not contain the given key.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    pub fn try_entry(&mut self, key: K) /* -> Result<Entry<???>, ()> */
    where
        K: Eq
    {
        todo!()
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
    /// todo!()
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
    /// todo!()
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
    /// todo!()
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
    /// todo!()
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
    /// todo!()
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
    /// todo!()
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
    /// todo!()
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

    // TODO: retain, into_keys, into_values
}

impl<K, V, S: Storage<ListMapLayout<K, V>>, I: Capacity> Drop for ListMap<K, V, S, I> {
    fn drop(&mut self) {
        self.clear()
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