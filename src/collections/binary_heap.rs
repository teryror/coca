//! A fixed-capacity priority queue implemented with a binary heap.
//!
//! Insertion and popping the largest element have O(log(n)) time complexity.
//! Checking the largest element is O(1).
//!
//! [`BinaryHeap<T, S, I>`](BinaryHeap) wraps a [`Vec<T, S, I>`](Vec) and
//! can therefore be converted into the underlying vector type at zero cost.
//! Converting a vector to a binary heap can be done in-place, and has O(n)
//! complexity. A binary heap can also be converted to a sorted vector in-place,
//! allowing it to be used for an O(n log(n)) in-place heap sort.

use crate::collections::vec::{Drain, Vec};
use crate::storage::{ArrayLayout, Capacity, Storage};

use core::fmt::{self, Debug, Formatter};
use core::iter::{FromIterator, FusedIterator};
#[allow(unused_imports)]
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut};

/// A fixed-capacity priority queue implemented with a binary heap.
///
/// This will be a max-heap, i.e. [`heap.pop()`](BinaryHeap::pop) will return
/// the largest value in the queue. [`core::cmp::Reverse`] or a custom `Ord`
/// implementation can be used to make a min-heap instead.
///
/// It is a logic error for an item to be modified in such a way that the
/// item's ordering relative to any other item, as determined by the `Ord`
/// trait, changes while it is in the heap. This is normally only possible
/// through `Cell`, `RefCell`, global state, I/O, or unsafe code.
pub struct BinaryHeap<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity = usize> {
    a: Vec<T, S, I>,
}

/// Structure wrapping a mutable reference to the greatest item on a `BinaryHeap`.
///
/// This `struct` is created by the [`BinaryHeap::peek_mut()`] method. See its
/// documentation for more.
pub struct PeekMut<'a, T: 'a + Ord, S: Storage<ArrayLayout<T>>, I: Capacity = usize> {
    heap: &'a mut BinaryHeap<T, S, I>,
}

impl<T: Ord + Debug, S: Storage<ArrayLayout<T>>, I: Capacity> Debug for PeekMut<'_, T, S, I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PeekMut").field(&self.heap.peek()).finish()
    }
}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> Drop for PeekMut<'_, T, S, I> {
    fn drop(&mut self) {
        heapify(self.heap.a.as_mut_slice(), 0);
    }
}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> Deref for PeekMut<'_, T, S, I> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        debug_assert!(!self.heap.is_empty());
        unsafe { self.heap.a.get_unchecked(0) }
    }
}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> DerefMut for PeekMut<'_, T, S, I> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        debug_assert!(!self.heap.is_empty());
        unsafe { self.heap.a.get_unchecked_mut(0) }
    }
}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> PeekMut<'_, T, S, I> {
    /// Removes the peeked value from the heap and returns it.
    pub fn pop(this: PeekMut<'_, T, S, I>) -> T {
        debug_assert!(!this.heap.is_empty());
        if let Some(value) = this.heap.pop() {
            core::mem::forget(this);
            value
        } else {
            unreachable!()
        }
    }
}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> From<S> for BinaryHeap<T, S, I> {
    /// Converts a contiguous block of memory into an empty binary heap.
    ///
    /// # Panics
    /// This may panic if the index type I cannot represent `buf.capacity()`.
    fn from(buf: S) -> Self {
        BinaryHeap { a: Vec::from(buf) }
    }
}

// This implementatin is largely based on the pseudocode given in
// CLRS - Introduction to Algorithms (third edition), Chapter 6

// These utility functions for binary tree traversal differ from the reference
// because we're using 0-based indexing, i.e. these are equivalent to
// `PARENT(i + 1) - 1`, `LEFT(i + 1) - 1`, and `RIGHT(i + 1) - 1`, respectively.
#[inline(always)]
fn parent(i: usize) -> usize {
    (i + 1) / 2 - 1
}

#[inline(always)]
fn left(i: usize) -> usize {
    2 * (i + 1) - 1
}

#[inline(always)]
fn right(i: usize) -> usize {
    2 * (i + 1)
}

fn heapify<T: Ord>(a: &mut [T], i: usize) {
    let l = left(i);
    let r = right(i);
    let mut largest = if l < a.len() && a[l] > a[i] { l } else { i };
    if r < a.len() && a[r] > a[largest] {
        largest = r;
    }
    if largest != i {
        a.swap(i, largest);
        heapify(a, largest);
    }
}

impl<T: Ord + Debug, S: Storage<ArrayLayout<T>>, I: Capacity> Debug for BinaryHeap<T, S, I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> From<Vec<T, S, I>> for BinaryHeap<T, S, I> {
    /// Converts a [`Vec`] into a binary heap.
    ///
    /// This conversion happens in-place, and has O(n) time complexity.
    fn from(mut vec: Vec<T, S, I>) -> Self {
        let a = vec.as_mut_slice();
        for i in (0..(a.len() / 2)).rev() {
            heapify(a, i);
        }
        BinaryHeap { a: vec }
    }
}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> BinaryHeap<T, S, I> {
    /// Returns a reference to the greatest item in the binary heap, or [`None`] if it is empty.
    #[inline]
    pub fn peek(&self) -> Option<&T> {
        self.a.first()
    }

    /// Returns a mutable reference to the greatest item in the binary heap, or
    /// [`None`] if it is empty.
    ///
    /// Note: If the `PeekMut` value is leaked, the heap may be left in an
    /// inconsistent state.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 3];
    /// let mut heap = coca::collections::SliceHeap::<_>::from(&mut backing_region[..]);
    /// heap.try_push(3);
    /// heap.try_push(5);
    /// heap.try_push(1);
    ///
    /// {
    ///     let mut val = heap.peek_mut().unwrap();
    ///     *val = 0;
    /// }
    ///
    /// assert_eq!(heap.pop(), Some(3));
    /// assert_eq!(heap.pop(), Some(1));
    /// assert_eq!(heap.pop(), Some(0));
    /// ```
    #[inline]
    pub fn peek_mut(&mut self) -> Option<PeekMut<T, S, I>> {
        if self.is_empty() {
            None
        } else {
            Some(PeekMut { heap: self })
        }
    }

    /// Removes the greatest element from the binary heap and returns it, or [`None`] if it is empty.
    ///
    /// # Examples
    /// ```
    /// use coca::collections::{SliceHeap, SliceVec};
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 3];
    /// let mut vec = SliceVec::<u32>::from(&mut backing_region[..]);
    /// vec.push(1); vec.push(3);
    ///
    /// let mut heap = SliceHeap::from(vec);
    ///
    /// assert_eq!(heap.pop(), Some(3));
    /// assert_eq!(heap.pop(), Some(1));
    /// assert_eq!(heap.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        let result = self.a.swap_remove(I::from_usize(0));
        heapify(self.a.as_mut_slice(), 0);
        Some(result)
    }

    /// Pushes an item onto the binary heap.
    ///
    /// # Panics
    /// Panics if the heap is already at capacity. See [`try_push`](BinaryHeap::try_push)
    /// for a checked version that never panics.
    #[inline]
    pub fn push(&mut self, item: T) {
        #[cold]
        #[inline(never)]
        fn assert_failed() -> ! {
            panic!("binary heap is already at capacity")
        }

        if self.try_push(item).is_err() {
            assert_failed();
        }
    }

    /// Pushes an item onto the binary heap, returning `Err(item)` if it is full.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 3];
    /// let mut heap = coca::collections::SliceHeap::<_>::from(&mut backing_region[..]);
    /// heap.try_push(3);
    /// heap.try_push(5);
    /// heap.try_push(1);
    ///
    /// assert_eq!(heap.len(), 3);
    /// assert_eq!(heap.peek(), Some(&5));
    /// ```
    pub fn try_push(&mut self, item: T) -> Result<(), T> {
        self.a.try_push(item)?;
        let a = self.a.as_mut_slice();
        let mut i = a.len() - 1;
        while i > 0 && a[parent(i)] < a[i] {
            a.swap(i, parent(i));
            i = parent(i);
        }
        Ok(())
    }

    /// Returns the number of elements the binary heap can hold.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.a.capacity()
    }

    /// Returns the number of elements in the binary heap, also referred to as its *length*.
    #[inline]
    pub fn len(&self) -> usize {
        self.a.len()
    }

    /// Returns `true` if the binary heap contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.a.is_empty()
    }

    /// Returns `true` if the binary heap contains the maximum number of elements.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.a.is_full()
    }

    /// Returns an iterator visiting all values in the underlying vector in arbitrary order.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.a.iter()
    }

    /// Clears the binary heap, returning an iterator over the removed elements.
    /// The elements are removed in arbitrary order.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 3];
    /// let mut heap = coca::collections::SliceHeap::<_>::from(&mut backing_region[..]);
    /// heap.push(1); heap.push(3);
    /// assert!(!heap.is_empty());
    ///
    /// let mut iter = heap.drain();
    /// assert!(iter.next().is_some());
    /// assert!(iter.next().is_some());
    /// assert!(iter.next().is_none());
    /// drop(iter);
    ///
    /// assert!(heap.is_empty());
    /// ```
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, T, S, I> {
        self.a.drain(..)
    }

    /// Returns an iterator which retrieves elements in heap order. The retrieved
    /// elements are removed from the original heap. The remaining elements will
    /// be removed on drop in heap order.
    ///
    /// # Remarks
    /// `.drain_sorted()` is O(n log(n)), much slower than [`.drain()`](BinaryHeap::drain).
    /// The latter is preferable in most cases.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 3];
    /// let mut heap = coca::collections::SliceHeap::<_>::from(&mut backing_region[..]);
    /// heap.push(1); heap.push(3); heap.push(5);
    ///
    /// let mut iter = heap.drain_sorted();
    /// assert_eq!(iter.next(), Some(5));
    /// drop(iter);
    /// assert!(heap.is_empty());
    /// ```
    #[inline]
    pub fn drain_sorted(&mut self) -> DrainSorted<'_, T, S, I> {
        DrainSorted { heap: self }
    }

    /// Drops all items from the binary heap.
    #[inline]
    pub fn clear(&mut self) {
        self.a.clear();
    }

    /// Consumes the `BinaryHeap` and returns the underlying vector in arbitrary order.
    #[inline]
    pub fn into_vec(self) -> Vec<T, S, I> {
        self.a
    }

    /// Consumes the `BinaryHeap` and returns a vector in sorted (ascending) order.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 5];
    /// let mut heap = coca::collections::SliceHeap::<_>::from(&mut backing_region[..]);
    /// heap.push(1); heap.push(5); heap.push(3); heap.push(2); heap.push(4);
    /// let vec = heap.into_sorted_vec();
    /// assert_eq!(vec, &[1, 2, 3, 4, 5][..]);
    /// ```
    pub fn into_sorted_vec(self) -> Vec<T, S, I> {
        let mut result = self.into_vec();
        let a = result.as_mut_slice();
        for i in (1..a.len()).rev() {
            a.swap(0, i);
            heapify(&mut a[..i], 0);
        }
        result
    }

    /// Consumes the `BinaryHeap` and returns an iterator which yields elements
    /// in heap order.
    ///
    /// When dropped, the remaining elements will be dropped in heap order.
    ///
    /// # Remarks
    /// `.into_iter_sorted()` is O(n log(n)), much slower than [`.into_iter()`](BinaryHeap::into_iter).
    /// The latter is preferable in most cases.
    ///
    /// # Examples
    /// ```
    /// let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 3];
    /// let mut heap = coca::collections::SliceHeap::<_>::from(&mut backing_region[..]);
    /// heap.push(1); heap.push(3); heap.push(5);
    ///
    /// let mut iter = heap.into_iter_sorted();
    /// assert_eq!(iter.next(), Some(5));
    /// assert_eq!(iter.next(), Some(3));
    /// assert_eq!(iter.next(), Some(1));
    /// ```
    pub fn into_iter_sorted(self) -> IntoIterSorted<T, S, I> {
        IntoIterSorted { heap: self }
    }
}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> IntoIterator for BinaryHeap<T, S, I> {
    type Item = T;
    type IntoIter = <Vec<T, S, I> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.a.into_iter()
    }
}

impl<T1, T2: Ord, S: Storage<ArrayLayout<T2>>, I: Capacity> Extend<T1> for BinaryHeap<T2, S, I>
where
    Vec<T2, S, I>: Extend<T1>,
{
    fn extend<T: IntoIterator<Item = T1>>(&mut self, iter: T) {
        self.a.extend(iter);
        for i in (0..(self.a.len() / 2)).rev() {
            heapify(self.a.as_mut_slice(), i);
        }
    }
}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> FromIterator<T> for BinaryHeap<T, S, I>
where
    Vec<T, S, I>: FromIterator<T>,
{
    /// Creates a binary heap from an iterator.
    ///
    /// # Panics
    /// Panics if the iterator yields more elements than the binary heap can hold.
    fn from_iter<It: IntoIterator<Item = T>>(iter: It) -> Self {
        let a = Vec::<T, S, I>::from_iter(iter);
        Self::from(a)
    }
}

/// A draining iterator over the elements of a `BinaryHeap`.
///
/// This `struct` is created by [`BinaryHeap::drain_sorted()`].
/// See its documentation for more.
pub struct DrainSorted<'a, T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> {
    heap: &'a mut BinaryHeap<T, S, I>,
}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> Iterator for DrainSorted<'_, T, S, I> {
    type Item = T;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.len();
        (size, Some(size))
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.heap.pop()
    }
}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> ExactSizeIterator
    for DrainSorted<'_, T, S, I>
{
}
impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> FusedIterator for DrainSorted<'_, T, S, I> {}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> Drop for DrainSorted<'_, T, S, I> {
    fn drop(&mut self) {
        self.for_each(drop);
    }
}

/// A consuming iterator that moves out of a `BinaryHeap`.
///
/// This `struct` is created by [`BinaryHeap::into_iter_sorted()`].
/// See its documentation for more.
#[derive(Debug)]
pub struct IntoIterSorted<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> {
    heap: BinaryHeap<T, S, I>,
}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> Iterator for IntoIterSorted<T, S, I> {
    type Item = T;

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.heap.len();
        (size, Some(size))
    }

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.heap.pop()
    }
}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> ExactSizeIterator
    for IntoIterSorted<T, S, I>
{
}
impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> FusedIterator for IntoIterSorted<T, S, I> {}

impl<T: Clone + Ord, S: Storage<ArrayLayout<T>>, I: Capacity> Clone for IntoIterSorted<T, S, I>
where
    BinaryHeap<T, S, I>: Clone,
{
    fn clone(&self) -> Self {
        self.heap.clone().into_iter_sorted()
    }
}

impl<T: Ord, S: Storage<ArrayLayout<T>>, I: Capacity> Drop for IntoIterSorted<T, S, I> {
    fn drop(&mut self) {
        self.for_each(drop);
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<T: Ord, I: Capacity> crate::collections::AllocHeap<T, I> {
    /// Constructs a new, empty `AllocHeap<T, I>` with the specified capacity.
    ///
    /// # Panics
    /// Panics if the specified capacity cannot be represented by a `usize`.
    pub fn with_capacity(capacity: I) -> Self {
        BinaryHeap {
            a: Vec::with_capacity(capacity),
        }
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<T: Clone + Ord, I: Capacity> Clone for crate::collections::AllocHeap<T, I> {
    fn clone(&self) -> Self {
        BinaryHeap { a: self.a.clone() }
    }
}

impl<T: Ord, I: Capacity, const C: usize> BinaryHeap<T, [MaybeUninit<T>; C], I> {
    /// Constructs a new, empty `BinaryHeap` backed by an inline array.
    ///
    /// # Panics
    /// Panics if `C` cannot be represented as a value of type `I`.
    ///
    /// # Examples
    /// ```
    /// let heap = coca::collections::InlineHeap::<char, 4>::new();
    /// assert_eq!(heap.capacity(), 4);
    /// assert!(heap.is_empty());
    /// ```
    pub fn new() -> Self {
        let a = Vec::new();
        BinaryHeap { a }
    }
}

impl<T: Ord, I: Capacity, const C: usize> Default for BinaryHeap<T, [MaybeUninit<T>; C], I> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + Ord, I: Capacity, const C: usize> Clone for BinaryHeap<T, [MaybeUninit<T>; C], I> {
    fn clone(&self) -> Self {
        BinaryHeap { a: self.a.clone() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tree_traversal_utilities() {
        assert_eq!(left(0), 1);
        assert_eq!(right(0), 2);
        assert_eq!(parent(1), 0);
        assert_eq!(parent(2), 0);

        for i in 1..=1000 {
            let l = left(i);
            let r = right(i);
            assert_eq!(l + 1, r);
            assert_eq!(parent(l), i);
            assert_eq!(parent(r), i);

            let ll = left(l);
            let lr = right(l);
            let rl = left(r);
            let rr = right(r);

            assert_eq!(ll + 1, lr);
            assert_eq!(rl + 1, rr);
            assert_eq!(parent(parent(ll)), i);
            assert_eq!(parent(parent(lr)), i);
            assert_eq!(parent(parent(rl)), i);
            assert_eq!(parent(parent(rr)), i);
        }
    }

    #[test]
    fn push_and_pop_randomized_inputs() {
        use rand::{rngs::SmallRng, RngCore, SeedableRng};

        let mut backing_region = [core::mem::MaybeUninit::<u32>::uninit(); 32];
        let mut heap = crate::collections::SliceHeap::<_>::from(&mut backing_region[..]);

        let mut rng = SmallRng::from_seed(crate::test_utils::RNG_SEED);

        let mut newest = 0;
        for _ in 0..32 {
            newest = rng.next_u32();
            heap.push(newest);
        }

        let mut prev = u32::max_value();
        for _ in 0..1000 {
            let x = heap.pop().unwrap();
            assert!(x <= prev || x == newest);
            prev = x;

            newest = rng.next_u32();
            heap.push(newest);
        }
    }

    #[test]
    fn iterators_take_and_drop_correctly() {
        use core::cell::RefCell;

        #[derive(Clone)]
        struct Droppable<'a, 'b> {
            value: usize,
            log: &'a RefCell<crate::collections::SliceVec<'b, usize>>,
        }

        impl PartialEq for Droppable<'_, '_> {
            fn eq(&self, rhs: &Self) -> bool {
                self.value == rhs.value
            }
        }

        impl Eq for Droppable<'_, '_> {}

        impl PartialOrd for Droppable<'_, '_> {
            fn partial_cmp(&self, rhs: &Self) -> Option<core::cmp::Ordering> {
                Some(self.cmp(rhs))
            }
        }

        impl Ord for Droppable<'_, '_> {
            fn cmp(&self, rhs: &Self) -> core::cmp::Ordering {
                self.value.cmp(&rhs.value)
            }
        }

        impl Drop for Droppable<'_, '_> {
            fn drop(&mut self) {
                self.log.borrow_mut().push(self.value);
            }
        }

        let mut backing_array = [MaybeUninit::<usize>::uninit(); 16];
        let drop_log = RefCell::new(crate::collections::SliceVec::<_>::from(
            &mut backing_array[..],
        ));

        let mut backing_region = [
            core::mem::MaybeUninit::<Droppable>::uninit(),
            core::mem::MaybeUninit::<Droppable>::uninit(),
            core::mem::MaybeUninit::<Droppable>::uninit(),
            core::mem::MaybeUninit::<Droppable>::uninit(),
            core::mem::MaybeUninit::<Droppable>::uninit(),
            core::mem::MaybeUninit::<Droppable>::uninit(),
            core::mem::MaybeUninit::<Droppable>::uninit(),
            core::mem::MaybeUninit::<Droppable>::uninit(),
        ];

        let mut heap = crate::collections::SliceHeap::<Droppable>::from(&mut backing_region[..]);
        for i in 1..=8 {
            heap.push(Droppable {
                value: i,
                log: &drop_log,
            });
        }

        let mut drain_iter = heap.drain_sorted();
        assert_eq!(drain_iter.next().unwrap().value, 8);
        assert_eq!(drain_iter.next().unwrap().value, 7);
        assert_eq!(drop_log.borrow().len(), 2);

        drop(drain_iter);
        assert_eq!(drop_log.borrow().len(), 8);
        assert_eq!(heap.len(), 0);

        for i in 1..=8 {
            heap.push(Droppable {
                value: i,
                log: &drop_log,
            });
        }

        let mut into_iter = heap.into_iter_sorted();
        assert_eq!(into_iter.next().unwrap().value, 8);
        assert_eq!(into_iter.next().unwrap().value, 7);
        assert_eq!(into_iter.next().unwrap().value, 6);
        assert_eq!(drop_log.borrow().len(), 11);

        drop(into_iter);
        assert_eq!(drop_log.borrow().len(), 16);

        assert_eq!(
            drop_log.borrow().as_slice(),
            &[8, 7, 6, 5, 4, 3, 2, 1, 8, 7, 6, 5, 4, 3, 2, 1]
        );
    }
}
