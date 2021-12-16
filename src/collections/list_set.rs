//! A set implemented with a vector.

use core::borrow::Borrow;
use core::slice::Iter;

use crate::collections::vec::{Vec, Drain};
use crate::storage::{ArrayLike, Capacity, Storage, InlineStorage};

/// A set implemented with a vector, using a linear scan to find a given value.
pub struct ListSet<T, S: Storage<ArrayLike<T>>, I: Capacity> {
    vec: Vec<T, S, I>,
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> From<S> for ListSet<T, S, I> {
    fn from(buf: S) -> Self {
        ListSet { vec: Vec::from(buf) }
    }
}

impl<T: Eq, S: Storage<ArrayLike<T>>, I: Capacity> From<Vec<T, S, I>> for ListSet<T, S, I> {
    fn from(mut vec: Vec<T, S, I>) -> Self {
        let mut i = 1;
        'outer: while i < vec.len() {
            for j in 0..i {
                let i = I::from_usize(i);
                let j = I::from_usize(j);

                if &vec[i] == &vec[j] {
                    vec.swap_remove(i);
                    continue 'outer;
                }
            }

            i += 1;
        }

        ListSet { vec }
    }
}

impl<T: Eq, S: Storage<ArrayLike<T>>, I: Capacity> ListSet<T, S, I> {
    /// Constructs a `ListSet` from a `Vec` without checking for duplicate elements.
    /// 
    /// It is a logic error to pass a vector containing elements that compare
    /// equal to one another; the behavior of the resulting set is unspecified,
    /// though it is guaranteed to be memory-safe.
    /// 
    /// If you cannot guarantee that this precondition holds, use the `ListSet::from`
    /// method provided by the [`From<Vec>`] implementation instead, which detects
    /// and removes duplicate entries.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::{InlineListSet, InlineVec};
    /// 
    /// let mut vec = InlineVec::<u32, 8>::new();
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    /// 
    /// let set = InlineListSet::from_vec_unchecked(vec);
    /// assert!(set.contains(&1));
    /// assert!(set.contains(&2));
    /// assert!(set.contains(&3));
    /// assert_eq!(set.len(), 3);
    /// ```
    #[inline]
    pub fn from_vec_unchecked(vec: Vec<T, S, I>) -> Self {
        ListSet { vec }
    }

    /// Converts a `ListSet` into the underlying `Vec`.
    #[inline]
    pub fn into_vec(self) -> Vec<T, S, I> {
        self.vec
    }

    /// Returns the number of elements the set can hold.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.vec.capacity()
    }

    /// Returns the number of elements in the set.
    #[inline]
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// Returns `true` if the set contains no elements, or `false` otherwise.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }

    /// Returns `true` if the set contains the maximum number of elements it can hold, or `false` otherwise.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.vec.is_full()
    }

    /// Clears the set, removing all values.
    /// 
    /// # Examples
    /// ```
    /// let mut set = coca::collections::InlineListSet::<u32, 4>::new();
    /// set.insert(1);
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.vec.clear();
    }

    /// An iterator visiting all elements of the set in arbitrary order. The iterator element type is `&'a T`.
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        self.vec.iter()
    }

    /// Clears the set, returning all elements in an iterator.
    /// 
    /// # Examples
    /// ```
    /// let mut set = coca::collections::InlineListSet::<u32, 4>::new();
    /// set.insert(1); set.insert(2); set.insert(3);
    /// 
    /// for i in set.drain() {
    ///     println!("{}", i);
    /// }
    /// 
    /// assert!(set.is_empty());
    /// ```
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, T, S, I> {
        self.vec.drain(..)
    }

    /// Returns `true` if the set contains a value equal to the given value, or `false` otherwise.
    /// 
    /// The value may be any borrowed form of the set's element type, but `Eq`
    /// on the borrowed form *must* match that of the element type.
    /// 
    /// # Examples
    /// ```
    /// let mut set = coca::collections::InlineListSet::<u32, 4>::new();
    /// set.insert(1);
    /// 
    /// assert_eq!(set.contains(&1), true);
    /// assert_eq!(set.contains(&2), false);
    /// ```
    #[inline]
    pub fn contains<Q: ?Sized + Eq>(&self, value: &Q) -> bool where T: Borrow<Q> {
        self.vec.iter().any(|item| item.borrow() == value)
    }

    /// Returns a reference to the value in the set, if any, that is equal to the given value.
    /// 
    /// The value may be any borrowed form of the set's element type, but `Eq`
    /// on the borrowed form *must* match that of the element type.
    /// 
    /// # Examples
    /// ```
    /// let mut set = coca::collections::InlineListSet::<u32, 4>::new();
    /// set.insert(1);
    /// 
    /// assert_eq!(set.get(&1), Some(&1));
    /// assert_eq!(set.get(&2), None);
    /// ```
    #[inline]
    pub fn get<Q: ?Sized + Eq>(&self, value: &Q) -> Option<&T> where T: Borrow<Q> {
        self.vec.iter().find(|item| (*item).borrow() == value)
    }

    /// Returns `true` if the set has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListSet;
    /// 
    /// let mut a = InlineListSet::<u32, 4>::new();
    /// a.insert(1); a.insert(2); a.insert(3);
    /// 
    /// let mut b = InlineListSet::<u32, 4>::new();
    /// assert_eq!(a.is_disjoint(&b), true);
    /// 
    /// b.insert(4);
    /// assert_eq!(a.is_disjoint(&b), true);
    /// 
    /// b.insert(1);
    /// assert_eq!(a.is_disjoint(&b), false);
    /// ```
    pub fn is_disjoint<S2: Storage<ArrayLike<T>>, I2: Capacity>(&self, other: &ListSet<T, S2, I2>) -> bool {
        for item in other.iter() {
            if self.contains(item) { return false; }
        }

        true
    }

    /// Returns `true` if the set is a subset of another,
    /// i.e. `other` contains at least all the values in `self`.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListSet;
    /// 
    /// let mut sup = InlineListSet::<u32, 4>::new();
    /// sup.insert(1); sup.insert(2); sup.insert(3);
    /// 
    /// let mut set = InlineListSet::<u32, 4>::new();
    /// assert_eq!(set.is_subset_of(&sup), true);
    /// 
    /// set.insert(2);
    /// assert_eq!(set.is_subset_of(&sup), true);
    /// 
    /// set.insert(5);
    /// assert_eq!(set.is_subset_of(&sup), false)
    /// ```
    pub fn is_subset_of<S2: Storage<ArrayLike<T>>, I2: Capacity>(&self, other: &ListSet<T, S2, I2>) -> bool {
        for item in self.iter() {
            if !other.contains(item) { return false; }
        }

        true
    }

    /// Returns `true` if the set is a superset of another,
    /// i.e. `self` contains at least all the values in `other`.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListSet;
    /// 
    /// let mut sub = InlineListSet::<u32, 4>::new();
    /// sub.insert(1); sub.insert(2);
    /// 
    /// let mut set = InlineListSet::<u32, 4>::new();
    /// assert_eq!(set.is_superset_of(&sub), false);
    /// 
    /// set.insert(0);
    /// set.insert(1);
    /// assert_eq!(set.is_superset_of(&sub), false);
    /// 
    /// set.insert(2);
    /// assert_eq!(set.is_superset_of(&sub), true);
    /// ```
    #[inline]
    pub fn is_superset_of<S2: Storage<ArrayLike<T>>, I2: Capacity>(&self, other: &ListSet<T, S2, I2>) -> bool {
        other.is_subset_of(self)
    }

    /// Adds a value to the set.
    /// 
    /// Returns `false` if the set already contained a value equal to
    /// the given value, or `true` otherwise. If such a value was already
    /// present, it is not updated; this matters for types that can be `==`
    /// without being identical.
    /// 
    /// # Panics
    /// Panics if the set did not contain the value, but no space remains to
    /// insert it. See [`try_insert`](ListSet::try_insert) for a checked version
    /// that never panics.
    #[inline]
    pub fn insert(&mut self, value: T) -> bool {
        self.try_insert(value).ok().expect("insufficient capacity")
    }

    /// Adds a value to the set.
    /// 
    /// Returns `Ok(false)` if the set already contained a value equal to
    /// the given value. Otherwise, returns `Ok(true)` if the given value
    /// was successfully inserted, or `Err(value)` if the remaining space
    /// is insufficient.
    /// 
    /// # Examples
    /// ```
    /// let mut set = coca::collections::InlineListSet::<u32, 4>::new();
    /// assert_eq!(set.capacity(), 4);
    /// 
    /// assert_eq!(set.try_insert(1), Ok(true));
    /// assert_eq!(set.try_insert(2), Ok(true));
    /// assert_eq!(set.try_insert(2), Ok(false));
    /// assert_eq!(set.len(), 2);
    /// 
    /// assert_eq!(set.try_insert(3), Ok(true));
    /// assert_eq!(set.try_insert(4), Ok(true));
    /// assert_eq!(set.try_insert(5), Err(5));
    /// assert_eq!(set.len(), 4);
    /// ```
    pub fn try_insert(&mut self, value: T) -> Result<bool, T> {
        if self.contains(&value) { return Ok(false); }
        self.vec.try_push(value).map(|_| true)
    }

    /// Inserts a value into the set without checking if it was already part of
    /// the set, and returns a reference to it.
    /// 
    /// It is a logic error to insert a duplicate element, and the behavior
    /// of the resulting set is unspecified, though it is guaranteed to be
    /// memory-safe.
    /// 
    /// This operation is faster than regular [`insert`](ListMap::insert),
    /// because it does not perform a lookup before insertion. This is useful
    /// during initial population of the set, e.g. when constructing a set from
    /// another set, which guarantees unique values.
    /// 
    /// # Panics
    /// Panics if the set is already at capacity. See
    /// [`try_insert_unique_unchecked`](ListMap::try_insert_unique_unchecked)
    /// for a checked version that never panics.
    #[inline]
    pub fn insert_unique_unchecked(&mut self, value: T) -> &T {
        self.try_insert_unique_unchecked(value).ok().expect("insufficient capacity")
    }

    /// Inserts a value into the set without checking if it was already part of
    /// the set.
    /// 
    /// Returns a reference to the inserted value, or `Err(value)` if the set
    /// is already full.
    /// 
    /// It is a logic error to insert a duplicate element, and the behavior
    /// of the resulting set is unspecified, though it is guaranteed to be
    /// memory-safe.
    /// 
    /// This operation is faster than regular [`try_insert`](ListMap::try_insert),
    /// because it does not perform a lookup before insertion. This is useful
    /// during initial population of the set, e.g. when constructing a set from
    /// another set, which guarantees unique values.
    pub fn try_insert_unique_unchecked(&mut self, value: T) -> Result<&T, T> {
        if self.vec.is_full() {
            Err(value)
        } else {
            self.vec.push(value);
            self.vec.last().ok_or_else(|| unreachable!())
        }
    }

    /// Adds a value to the set, replacing the existing value, if any, that is
    /// equal to the given one. This matters for types that can be `==` without
    /// being identical.
    /// 
    /// Returns the replaced value.
    /// 
    /// # Panics
    /// Panics if the set is full and does not contain any values equal to
    /// the given one. See [`try_replace`](ListSet::try_replace) for a checked
    /// version that never panics.
    pub fn replace(&mut self, value: T) -> Option<T> {
        self.try_replace(value).ok().expect("insufficient capacity")
    }

    /// Adds a value to the set, replacing the existing value, if any, that is
    /// equal to the given one. This matters for types that can be `==` without
    /// being identical.
    /// 
    /// Returns the replaced value, or `Ok(None)` if the value was successfully
    /// inserted without replacing any other element, or `Err(value)` if the
    /// set was already full.
    /// 
    /// # Examples
    /// ```
    /// struct Foo(u32, u32);
    /// impl Eq for Foo {}
    /// impl PartialEq for Foo {
    ///     fn eq(&self, other: &Foo) -> bool {
    ///         self.0 == other.0
    ///     }
    /// }
    /// 
    /// let mut set = coca::collections::InlineListSet::<Foo, 3>::new();
    /// set.insert(Foo(1, 0));
    /// 
    /// if let Ok(Some(foo)) = set.try_replace(Foo(1, 10)) {
    ///     assert_eq!(foo.0, 1);
    ///     assert_eq!(foo.1, 0);
    /// }
    /// # else {
    /// #     unreachable!();
    /// # }
    /// 
    /// set.insert(Foo(2, 0));
    /// set.insert(Foo(3, 0));
    /// 
    /// assert!(set.try_replace(Foo(4, 10)).is_err());
    /// ```
    pub fn try_replace(&mut self, value: T) -> Result<Option<T>, T> {
        if let Some((idx, _)) = self.vec.iter().enumerate().find(|(_, item)| *item ==  &value) {
            Ok(Some(self.vec.replace(I::from_usize(idx), value)))
        } else if self.is_full() {
            Err(value)
        } else {
            self.vec.push(value);
            Ok(None)
        }
    }

    /// Removes a value from the set, and returns whether it was previously present.
    /// 
    /// The given value may be any borrowed form of the set's element type,
    /// but `Eq` on the borrowed form *must* match that of the element type.
    /// 
    /// # Examples
    /// ```
    /// let mut set = coca::collections::InlineListSet::<u32, 4>::new();
    /// set.insert(2);
    /// 
    /// assert_eq!(set.remove(&2), true);
    /// assert_eq!(set.remove(&2), false);
    /// ```
    pub fn remove<Q: ?Sized + Eq>(&mut self, value: &Q) -> bool where T: Borrow<Q> {
        if let Some((idx, _)) = self.vec.iter().enumerate().find(|(_, item)| (*item).borrow() == value) {
            self.vec.swap_remove(I::from_usize(idx));
            true
        } else {
            false
        }
    }

    /// Removes and returns the value from the set, if any, that is equal to the given one.
    /// 
    /// The given value may be any borrowed form of the set's element type,
    /// but `Eq` on the borrowed form *must* match that of the element type.
    /// 
    /// # Examples
    /// ```
    /// let mut set = coca::collections::InlineListSet::<u32, 4>::new();
    /// set.insert(2);
    /// 
    /// assert_eq!(set.take(&2), Some(2));
    /// assert_eq!(set.take(&2), None);
    /// ```
    pub fn take<Q: ?Sized + Eq>(&mut self, value: &Q) -> Option<T> where T: Borrow<Q> {
        if let Some((idx, _)) = self.vec.iter().enumerate().find(|(_, item)| (*item).borrow() == value) {
            Some(self.vec.swap_remove(I::from_usize(idx)))
        } else {
            None
        }
    }

    /// Retains only the elements specified by the predicate.
    /// 
    /// In other words, removes all elements `e` such that `f(&e)` returns `false`.
    /// The elements are visited in unsorted (and unspecified) order.
    /// 
    /// # Examples
    /// ```
    /// let mut set = coca::collections::InlineListSet::<u32, 8>::new();
    /// (0..8).for_each(|x| { set.insert(x); });
    /// set.retain(|&x| x % 2 == 0);
    /// assert_eq!(set.len(), 4);
    /// ```
    #[inline]
    pub fn retain<F: FnMut(&T) -> bool>(&mut self, pred: F) {
        self.vec.retain(pred);
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<T, I: Capacity> crate::collections::AllocListSet<T, I> {
    /// Constructs a new, empty [`AllocListSet`](crate::collections::AllocListSet)
    /// with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        let storage = crate::storage::AllocStorage::with_capacity(capacity);
        Self::from(storage)
    }
}

impl<T, I: Capacity, const N: usize> ListSet<T, InlineStorage<T, N>, I> {
    /// Constructs a new, empty [`InlineListSet`](crate::collections::InlineListSet).
    pub fn new() -> Self {
        ListSet { vec: crate::collections::TiInlineVec::<T, I, N>::new() }
    }
}

impl<T, I: Capacity, const N: usize> Default for ListSet<T, InlineStorage<T, N>, I> {
    fn default() -> Self {
        Self::new()
    }
}