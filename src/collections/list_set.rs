//! A set implemented with a vector.

use core::borrow::Borrow;
use core::fmt::Debug;
use core::iter::FusedIterator;
use core::slice::Iter;

use crate::collections::vec::{Vec, Drain};
use crate::storage::{ArrayLike, Capacity, Storage, InlineStorage};

/// A set implemented with a vector, using a linear scan to find a given value.
/// 
/// This is simple and cache-friendly, though algorithmically inefficient:
/// converting an *n*-element [`Vec`] into a set requires *O*(*n*²) comparisons
/// and looking up a value requires *O*(*n*) comparisons. Set operators such as
/// [`difference`], [`intersection`], and [`union`] require *O*(*n* · *m*)
/// comparisons.
/// 
/// [`difference`]: ListSet::difference
/// [`intersection`]: ListSet::intersection
/// [`union`]: ListSet::union
/// 
/// Newly inserted elements are appended to the internal vector, and a removed
/// element is replaced by the last one in the list, meaning modifications have
/// constant overhead after the initial lookup. This also means insertion order
/// is **not** preserved.
/// 
/// As with the [`ListMap`](crate::collections::list_map::ListMap) type, a
/// `ListSet` requires that the element type implements the [`Eq`] trait.
/// This can frequently be achieved by using `#[derive(PartialEq, Eq)]`.
/// 
/// It is a logic error for an item to be modified in such a way that its
/// equality, as determined by the `Eq` trait, changes while it is in the set.
/// This is normally only possible through [`Cell`](core::cell::Cell),
/// [`RefCell`](core::cell::RefCell), global state, I/O, or unsafe code. The
/// behavior resulting from such a logic error is not specified, but will not
/// result in undefined behavior. This could include panics, incorrect results,
/// aborts, memory leaks, and non-termination.
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

                if vec[i] == vec[j] {
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

    /// Converts a `ListSet` into the underlying `Vec`.
    #[inline]
    pub fn into_vec(self) -> Vec<T, S, I> {
        self.vec
    }

    /// Returns a slice of all elements contained in the set in arbitrary order.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self.vec.as_slice()
    }

    /// An iterator visiting all elements of the set in arbitrary order. The iterator element type is `&'a T`.
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        self.vec.iter()
    }

    /// Returns an iterator visiting the values representing the set difference,
    /// i.e. the values that are in `self` but not in `other`.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListSet;
    /// let mut a = InlineListSet::<u32, 4>::new();
    /// (1..4).for_each(|x| { a.insert(x); });
    /// 
    /// let mut b = InlineListSet::<u32, 4>::new();
    /// (2..5).for_each(|x| { b.insert(x); });
    /// 
    /// let mut d = InlineListSet::<u32, 4>::new();
    /// a.difference(&b).for_each(|x| { d.insert(*x); });
    /// assert_eq!(d.as_slice(), &[1]);
    /// 
    /// d.clear();
    /// b.difference(&a).for_each(|x| { d.insert(*x); });
    /// assert_eq!(d.as_slice(), &[4]);
    /// ```
    #[inline]
    pub fn difference<'a, S2: Storage<ArrayLike<T>>, I2: Capacity>(&'a self, other: &'a ListSet<T, S2, I2>) -> Difference<'a, T> {
        Difference { this: self.as_slice(), other: other.as_slice(), front: 0 }
    }

    /// Returns an iterator visiting the values representing the symmetric difference,
    /// i.e. the values that are in `self` or in `other`, but not both.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::{InlineListSet, InlineVec};
    /// let mut a = InlineListSet::<u32, 4>::new();
    /// (1..4).for_each(|x| { a.insert(x); });
    /// 
    /// let mut b = InlineListSet::<u32, 4>::new();
    /// (2..5).for_each(|x| { b.insert(x); });
    /// 
    /// let mut d = InlineVec::<u32, 4>::new();
    /// d.extend(a.symmetric_difference(&b).cloned());
    /// d.sort();
    /// 
    /// assert_eq!(&d, &[1, 4]);
    /// ```
    #[inline]
    pub fn symmetric_difference<'a, S2: Storage<ArrayLike<T>>, I2: Capacity>(&'a self, other: &'a ListSet<T, S2, I2>) -> SymmetricDifference<'a, T> {
        SymmetricDifference { this: self.as_slice(), other: other.as_slice(), front: 0 }
    }

    /// Returns an iterator visiting the values representing the intersection,
    /// i.e. the values that are both in `self` and `other`.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::{InlineListSet, InlineVec};
    /// let mut a = InlineListSet::<u32, 4>::new();
    /// (1..4).for_each(|x| { a.insert(x); });
    /// 
    /// let mut b = InlineListSet::<u32, 4>::new();
    /// (2..5).for_each(|x| { b.insert(x); });
    /// 
    /// let mut i = InlineVec::<u32, 4>::new();
    /// i.extend(a.intersection(&b).cloned());
    /// i.sort();
    /// 
    /// assert_eq!(&i, &[2, 3]);
    /// ```
    #[inline]
    pub fn intersection<'a, S2: Storage<ArrayLike<T>>, I2: Capacity>(&'a self, other: &'a ListSet<T, S2, I2>) -> Intersection<'a, T> {
        Intersection { this: self.as_slice(), other: other.as_slice(), front: 0 }
    }

    /// Returns an iterator visiting the values representing the union,
    /// i.e. all values in `self` or `other`, without duplicates.
    /// 
    /// # Examples
    /// ```
    /// use coca::collections::InlineListSet;
    /// let mut a = InlineListSet::<u32, 4>::new();
    /// (1..4).for_each(|x| { a.insert(x); });
    /// 
    /// let mut b = InlineListSet::<u32, 4>::new();
    /// (2..5).for_each(|x| { b.insert(x); });
    /// 
    /// let mut u = InlineListSet::<u32, 4>::new();
    /// a.union(&b).for_each(|x| { u.insert_unique_unchecked(*x); });
    /// (1..5).for_each(|x| assert!(u.contains(&x)));
    /// ```
    #[inline]
    pub fn union<'a, S2: Storage<ArrayLike<T>>, I2: Capacity>(&'a self, other: &'a ListSet<T, S2, I2>) -> Union<'a, T> {
        Union { this: self.as_slice(), other: other.as_slice(), front: 0 }
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
    /// This operation is faster than regular [`insert`](ListSet::insert),
    /// because it does not perform a lookup before insertion. This is useful
    /// during initial population of the set, e.g. when constructing a set from
    /// another set, which guarantees unique values.
    /// 
    /// # Panics
    /// Panics if the set is already at capacity. See
    /// [`try_insert_unique_unchecked`](ListSet::try_insert_unique_unchecked)
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
    /// This operation is faster than regular [`try_insert`](ListSet::try_insert),
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

impl<T: Eq, S1, S2, I1, I2> core::ops::BitAndAssign<&'_ ListSet<T, S2, I2>> for ListSet<T, S1, I1>
where
    S1: Storage<ArrayLike<T>>,
    S2: Storage<ArrayLike<T>>,
    I1: Capacity,
    I2: Capacity,
{
    fn bitand_assign(&mut self, rhs: &ListSet<T, S2, I2>) {
        let mut i = 0;
        while i < self.len() {
            if rhs.contains(&self.vec.as_slice()[i]) {
                i += 1;
            } else {
                self.vec.swap_remove(I1::from_usize(i));
            }
        }
    }
}

impl<T, S1, S2, I1, I2> core::ops::BitOrAssign<&'_ ListSet<T, S2, I2>> for ListSet<T, S1, I1>
where
    T: Clone + Eq,
    S1: Storage<ArrayLike<T>>,
    S2: Storage<ArrayLike<T>>,
    I1: Capacity,
    I2: Capacity,
{
    fn bitor_assign(&mut self, rhs: &ListSet<T, S2, I2>) {
        for x in rhs.iter() {
            if !self.contains(x) {
                self.insert_unique_unchecked(x.clone());
            }
        }
    }
}

impl<T: Debug, S: Storage<ArrayLike<T>>, I: Capacity> Debug for ListSet<T, S, I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_set().entries(self.vec.as_slice()).finish()
    }
}

impl<T: Eq, S: Storage<ArrayLike<T>>, I: Capacity> Extend<T> for ListSet<T, S, I> {
    fn extend<It: IntoIterator<Item = T>>(&mut self, iter: It) {
        iter.into_iter().for_each(|x| { self.insert(x); });
    }
}

impl<'a, T: Clone + Eq, S: Storage<ArrayLike<T>>, I: Capacity> Extend<&'a T> for ListSet<T, S, I> {
    fn extend<It: IntoIterator<Item = &'a T>>(&mut self, iter: It) {
        iter.into_iter().for_each(|x| { self.insert(x.clone()); });
    }
}

impl<T, S: Storage<ArrayLike<T>>, I: Capacity> IntoIterator for ListSet<T, S, I> {
    type IntoIter = crate::collections::vec::IntoIterator<T, S, I>;
    type Item = T;

    fn into_iter(self) -> Self::IntoIter {
        self.vec.into_iter()
    }
}

impl<'a, T: Eq, S: Storage<ArrayLike<T>>, I: Capacity> IntoIterator for &'a ListSet<T, S, I> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

impl<T, S1, S2, I1, I2> PartialEq<ListSet<T, S2, I2>> for ListSet<T, S1, I1>
where
    S1: Storage<ArrayLike<T>>,
    S2: Storage<ArrayLike<T>>,
    I1: Capacity,
    I2: Capacity,
    T: Eq,
{
    fn eq(&self, other: &ListSet<T, S2, I2>) -> bool {
        self.is_subset_of(other) && self.is_superset_of(other)
    }
}

impl<T: Eq, S: Storage<ArrayLike<T>>, I: Capacity> Eq for ListSet<T, S, I> {}

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
        ListSet { vec: crate::collections::InlineVec::<T, N, I>::new() }
    }
}

impl<T, I: Capacity, const N: usize> Default for ListSet<T, InlineStorage<T, N>, I> {
    fn default() -> Self {
        Self::new()
    }
}

/// A lazy iterator producing elements in the difference between two [`ListSet`]s.
/// 
/// This `struct` is created by the [`difference`](ListSet::difference)
/// method on `ListSet`. See its documentation for more.
pub struct Difference<'a, T> {
    this: &'a [T],
    other: &'a [T],
    front: usize,
}

impl<'a, T: Eq> Iterator for Difference<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        'outer: while self.front < self.this.len() {
            let my_item = &self.this[self.front];
            self.front += 1;

            for their_item in self.other {
                if my_item == their_item {
                    continue 'outer;
                }
            }

            return Some(my_item);
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let max_len = self.this.len() - self.front;
        (0, Some(max_len))
    }
}

impl<T: Eq> FusedIterator for Difference<'_, T> {}

/// A lazy iterator producing elements in the symmetric difference of [`ListSet`]s.
/// 
/// This `struct` is created by the [`symmetric_difference`](ListSet::symmetric_difference)
/// method on `ListSet`. See its documentation for more.
pub struct SymmetricDifference<'a, T> {
    this: &'a [T],
    other: &'a [T],
    front: usize,
}

impl<'a, T: Eq> Iterator for SymmetricDifference<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        'outer1: while self.front < self.this.len() {
            let my_item = &self.this[self.front];
            self.front += 1;

            for their_item in self.other {
                if my_item == their_item {
                    continue 'outer1;
                }
            }

            return Some(my_item);
        }

        'outer2: while (self.front - self.this.len()) < self.other.len() {
            let their_item = &self.other[self.front - self.this.len()];
            self.front += 1;

            for my_item in self.this {
                if my_item == their_item {
                    continue 'outer2;
                }
            }

            return Some(their_item);
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let max_len = if self.front < self.this.len() {
            (self.this.len() - self.front) + self.other.len()
        } else {
            self.other.len() - (self.front - self.this.len())
        };

        (0, Some(max_len))
    }
}

impl<T: Eq> FusedIterator for SymmetricDifference<'_, T> {}

/// A lazy iterator producing elements in the intersection of [`ListSet`]s.
/// 
/// This struct is created by the [`intersection`](ListSet::intersection)
/// method on `ListSet`. See its documentation for more.
pub struct Intersection<'a, T> {
    this: &'a [T],
    other: &'a [T],
    front: usize,
}

impl<'a, T: Eq> Iterator for Intersection<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        while self.front < self.this.len() {
            let my_item = &self.this[self.front];
            self.front += 1;

            for their_item in self.other {
                if my_item == their_item {
                    return Some(my_item);
                }
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let max_len = self.this.len() - self.front;
        (0, Some(max_len))
    }
}

impl<T: Eq> FusedIterator for Intersection<'_, T> {}

/// A lazy iterator producing elements in the union of [`ListSet`]s.
/// 
/// This `struct` is created by the [`union`](ListSet::union)
/// method on `ListSet`. See its documentation for more.
pub struct Union<'a, T> {
    this: &'a [T],
    other: &'a [T],
    front: usize,
}

impl<'a, T: Eq> Iterator for Union<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.front < self.this.len() {
            let result = &self.this[self.front];
            self.front += 1;
            return Some(result);
        }

        'outer: while (self.front - self.this.len()) < self.other.len() {
            let their_item = &self.other[self.front - self.this.len()];
            self.front += 1;

            for my_item in self.this {
                if my_item == their_item {
                    continue 'outer;
                }
            }

            return Some(their_item);
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let min_len = self.this.len().saturating_sub(self.front);
        let max_len = if self.front < self.this.len() {
            self.other.len() + min_len
        } else {
            self.other.len() - self.front
        };

        (min_len, Some(max_len))
    }
}

impl<T: Eq> FusedIterator for Union<'_, T> {}