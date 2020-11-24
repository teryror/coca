use crate::arena::Box;

use core::convert::{AsMut, AsRef, TryInto};
use core::hash::{Hash, Hasher};
use core::iter::{IntoIterator as IntoIter, Iterator};
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ptr;

// TODO: Should this be unsafe to implement? Soundness of unsafe code depends on this, right!?
pub trait AsIndex: Copy + Sized {
    fn from_usize(value: usize) -> Self;
    fn to_usize(self) -> usize;
}

impl AsIndex for u8 {
    fn from_usize(value: usize) -> Self {
        value.try_into().unwrap()
    }
    fn to_usize(self) -> usize {
        self.into()
    }
}

impl AsIndex for u16 {
    fn from_usize(value: usize) -> Self {
        value.try_into().unwrap()
    }
    fn to_usize(self) -> usize {
        self.into()
    }
}

impl AsIndex for u32 {
    fn from_usize(value: usize) -> Self {
        value.try_into().unwrap()
    }
    fn to_usize(self) -> usize {
        self.try_into().unwrap()
    }
}

impl AsIndex for u64 {
    fn from_usize(value: usize) -> Self {
        value.try_into().unwrap()
    }
    fn to_usize(self) -> usize {
        self.try_into().unwrap()
    }
}

impl AsIndex for usize {
    fn from_usize(value: usize) -> Self {
        value
    }
    fn to_usize(self) -> usize {
        self
    }
}

#[macro_export]
macro_rules! index_type {
    ($v:vis $name:ident: $repr:ty) => {
        #[derive(
            core::marker::Copy,
            core::clone::Clone,
            core::default::Default,
            core::hash::Hash,
            core::cmp::PartialEq,
            core::cmp::Eq,
            core::cmp::PartialOrd,
            core::cmp::Ord)]
        $v struct $name($repr);

        impl $crate::list::AsIndex for $name {
            fn from_usize(value: usize) -> Self {
                Self(<$repr as AsIndex>::from_usize(value))
            }

            fn to_usize(self) -> usize {
                <$repr as AsIndex>::to_usize(self.0)
            }
        }
    }
}

pub type BoxSliceList<'src, E, I = usize> = List<E, Box<'src, [MaybeUninit<E>]>, I>;

#[cfg(feature = "nightly")]
pub type BoxArrayList<'src, E, I, const N: usize> = List<E, Box<'src, [MaybeUninit<E>; N]>, I>;

pub struct List<Element, Buf, Idx = usize>
where
    Buf: AsRef<[MaybeUninit<Element>]> + AsMut<[MaybeUninit<Element>]>,
    Idx: AsIndex,
{
    len: Idx,
    buf: Buf,
    elem: PhantomData<Element>,
}

impl<E, B, I> List<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buf.as_ref().len()
    }

    #[inline]
    pub fn from_buffer(buf: B) -> Self {
        List {
            len: I::from_usize(0),
            buf,
            elem: PhantomData,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len.to_usize()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len.to_usize() == 0
    }

    #[inline]
    pub fn is_full(&self) -> bool {
        self.len.to_usize() == self.buf.as_ref().len()
    }

    #[inline]
    pub fn pop(&mut self) -> Option<E> {
        if self.is_empty() {
            return None;
        }

        self.len = I::from_usize(self.len() - 1);
        unsafe { Some(self.buf.as_ref()[self.len()].as_ptr().read()) }
    }

    #[inline]
    pub fn as_slice(&self) -> &[E] {
        self
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [E] {
        self
    }

    #[inline]
    pub fn get(&self, index: I) -> Option<&E> {
        let index = index.to_usize();
        if self.len() <= index {
            return None;
        }

        unsafe { Some(self.buf.as_ref()[index].as_ptr().as_ref().unwrap()) }
    }

    #[inline]
    pub fn get_mut(&mut self, index: I) -> Option<&mut E> {
        let index = index.to_usize();
        if self.len() <= index {
            return None;
        }

        unsafe { Some(self.buf.as_mut()[index].as_mut_ptr().as_mut().unwrap()) }
    }

    #[inline]
    pub fn try_push(&mut self, value: E) -> Result<(), E> {
        if self.is_full() {
            return Err(value);
        }

        let len = self.len();
        let p = self.buf.as_mut()[len].as_mut_ptr();
        unsafe {
            p.write(value);
        }

        self.len = I::from_usize(len + 1);
        Ok(())
    }

    #[inline]
    pub fn push(&mut self, value: E) {
        #[cold]
        #[inline(never)]
        fn assert_failed() -> ! {
            panic!("list is already at capacity")
        }

        if self.try_push(value).is_err() {
            assert_failed();
        }
    }

    pub fn truncate(&mut self, len: I) {
        let new_len = len.to_usize();
        let old_len = self.len.to_usize();

        if new_len >= old_len {
            return;
        }

        for i in new_len..old_len {
            unsafe {
                self.buf.as_mut()[i].as_mut_ptr().drop_in_place();
            }
        }

        self.len = len;
    }

    #[inline]
    pub fn clear(&mut self) {
        self.truncate(I::from_usize(0))
    }

    #[inline]
    pub fn swap(&mut self, fst: I, snd: I) {
        let fst = fst.to_usize();
        let snd = snd.to_usize();
        self.as_mut_slice().swap(fst, snd);
    }

    #[inline]
    pub fn swap_remove(&mut self, index: I) -> E {
        #[cold]
        #[inline(never)]
        fn assert_failed(idx: usize, len: usize) -> ! {
            panic!(
                "swap_remove index (is {}) should be < len (is {})",
                idx, len
            );
        }

        let idx = index.to_usize();
        let len = self.len.to_usize();
        if idx >= len {
            assert_failed(idx, len);
        }

        unsafe {
            let last = ptr::read(self.buf.as_ref()[len - 1].as_ptr());
            let hole = self.buf.as_mut()[idx].as_mut_ptr();
            self.len = I::from_usize(self.len() - 1);
            ptr::replace(hole, last)
        }
    }

    pub fn insert(&mut self, index: I, element: E) {
        #[cold]
        #[inline(never)]
        fn assert_failed() -> ! {
            panic!("list is already at capacity")
        }

        let result = self.try_insert(index, element);
        if result.is_err() {
            assert_failed();
        }
    }

    pub fn try_insert(&mut self, index: I, element: E) -> Result<(), E> {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!(
                "insertion index (is {}) should be <= len (is {})",
                index, len
            );
        }

        if self.is_full() {
            return Err(element);
        }

        let idx = index.to_usize();
        let len = self.len.to_usize();
        if idx > len {
            assert_failed(idx, len);
        }

        unsafe {
            let p = self.buf.as_mut()[idx].as_mut_ptr();
            ptr::copy(p, p.offset(1), len - idx);
            ptr::write(p, element);
        }

        self.len = I::from_usize(len + 1);
        Ok(())
    }

    pub fn remove(&mut self, index: I) -> E {
        #[cold]
        #[inline(never)]
        fn assert_failed(idx: usize, len: usize) -> ! {
            panic!("removal index (is {}) should be < len (is {})", idx, len);
        }

        let idx = index.to_usize();
        let len = self.len.to_usize();
        if idx >= len {
            assert_failed(idx, len);
        }

        unsafe {
            let ret;
            {
                let p = self.buf.as_mut()[idx].as_mut_ptr();
                ret = ptr::read(p);
                ptr::copy(p.offset(1), p, len - idx - 1);
            }

            self.len = I::from_usize(len - 1);
            ret
        }
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&E) -> bool,
    {
        let len = self.len.to_usize();
        let mut del = 0;
        unsafe {
            for idx in 0..len {
                let p = self.buf.as_mut()[idx].as_mut_ptr();
                if !f(p.as_mut().unwrap()) {
                    del += 1;
                } else if del > 0 {
                    ptr::swap(p, p.sub(del))
                }
            }
        }
        if del > 0 {
            self.truncate(I::from_usize(len - del));
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &E> {
        self.into_iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut E> {
        self.into_iter()
    }
}

impl<E, B, I> core::ops::Deref for List<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    type Target = [E];
    fn deref(&self) -> &[E] {
        unsafe { core::slice::from_raw_parts(self.buf.as_ref()[0].as_ptr(), self.len.to_usize()) }
    }
}

impl<E, B, I> core::ops::DerefMut for List<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    fn deref_mut(&mut self) -> &mut [E] {
        unsafe {
            core::slice::from_raw_parts_mut(self.buf.as_mut()[0].as_mut_ptr(), self.len.to_usize())
        }
    }
}

impl<E, B, I> core::ops::Index<I> for List<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    type Output = E;
    fn index(&self, index: I) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<E, B, I> core::ops::IndexMut<I> for List<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.get_mut(index).unwrap()
    }
}

macro_rules! _impl_idx_range {
    ($self:ident, $idx:ident: $r:ty, $lo:expr, $hi:expr) => {
        impl<E, B, I> core::ops::Index<$r> for List<E, B, I>
        where
            B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
            I: AsIndex + PartialOrd,
        {
            type Output = [E];
            #[allow(unused_variables)]
            fn index(&self, $idx: $r) -> &Self::Output {
                let $self = self;
                let start = $lo;
                let end = $hi;
                &self.as_slice()[start..end]
            }
        }

        impl<E, B, I> core::ops::IndexMut<$r> for List<E, B, I>
        where
            B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
            I: AsIndex + PartialOrd,
        {
            #[allow(unused_variables)]
            fn index_mut(&mut self, $idx: $r) -> &mut Self::Output {
                let (start, end) = {
                    let $self = &self;
                    ($lo, $hi)
                };
                &mut self.as_mut_slice()[start..end]
            }
        }
    };
}

_impl_idx_range! { s, index: core::ops::Range<I>, index.start.to_usize(), index.end.to_usize() }
_impl_idx_range! { s, index: core::ops::RangeFrom<I>, index.start.to_usize(), s.len() }
_impl_idx_range! { s, index: core::ops::RangeFull, 0, s.len() }
_impl_idx_range! { s, index: core::ops::RangeInclusive<I>, index.start().to_usize(), index.end().to_usize() + 1 }
_impl_idx_range! { s, index: core::ops::RangeTo<I>, 0, index.end.to_usize() }
_impl_idx_range! { s, index: core::ops::RangeToInclusive<I>, 0, index.end.to_usize() + 1 }

impl<E, B, I> core::convert::AsRef<[E]> for List<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    fn as_ref(&self) -> &[E] {
        self
    }
}

impl<E, B, I> core::convert::AsMut<[E]> for List<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    fn as_mut(&mut self) -> &mut [E] {
        self
    }
}

impl<E, B, I> core::ops::Drop for List<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                self.buf.as_mut()[0].as_mut_ptr(),
                self.len(),
            ))
        }
    }
}

impl<E, B, I> core::fmt::Debug for List<E, B, I>
where
    E: core::fmt::Debug,
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<E, B, I> Hash for List<E, B, I>
where
    E: Hash,
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

impl<AE, AB, AI, BE, BB, BI> core::cmp::PartialEq<List<BE, BB, BI>> for List<AE, AB, AI>
where
    AE: core::cmp::PartialEq<BE>,
    AB: AsRef<[MaybeUninit<AE>]> + AsMut<[MaybeUninit<AE>]>,
    BB: AsRef<[MaybeUninit<BE>]> + AsMut<[MaybeUninit<BE>]>,
    AI: AsIndex,
    BI: AsIndex,
{
    #[inline]
    fn eq(&self, other: &List<BE, BB, BI>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<E, B, I> core::cmp::Eq for List<E, B, I>
where
    E: core::cmp::Eq,
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
}

impl<V, E, B, I> core::cmp::PartialEq<&[V]> for List<E, B, I>
where
    E: core::cmp::PartialEq<V>,
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    #[inline]
    fn eq(&self, other: &&[V]) -> bool {
        self.as_slice() == &other[..]
    }
}

impl<V, E, B, I> core::cmp::PartialEq<&mut [V]> for List<E, B, I>
where
    E: core::cmp::PartialEq<V>,
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    #[inline]
    fn eq(&self, other: &&mut [V]) -> bool {
        self.as_slice() == &other[..]
    }
}

impl<V, E, B, I> core::cmp::PartialEq<List<E, B, I>> for &[V]
where
    V: core::cmp::PartialEq<E>,
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    #[inline]
    fn eq(&self, other: &List<E, B, I>) -> bool {
        &self[..] == other.as_slice()
    }
}

impl<V, E, B, I> core::cmp::PartialEq<List<E, B, I>> for &mut [V]
where
    V: core::cmp::PartialEq<E>,
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    #[inline]
    fn eq(&self, other: &List<E, B, I>) -> bool {
        &self[..] == other.as_slice()
    }
}

impl<E, B, I> core::cmp::PartialOrd for List<E, B, I>
where
    E: core::cmp::PartialOrd,
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}

impl<E, B, I> core::cmp::Ord for List<E, B, I>
where
    E: core::cmp::Ord,
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_slice().cmp(&other.as_slice())
    }
}

pub struct IntoIterator<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    start: I,
    end: I,
    buf: B,
    elems: PhantomData<E>,
}

impl<E, B, I> Iterator for IntoIterator<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    type Item = E;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.end.to_usize() - self.start.to_usize();
        (size, Some(size))
    }

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.start.to_usize();
        let end = self.end.to_usize();
        if start >= end {
            return None;
        }

        let ret = unsafe { self.buf.as_ref()[start].as_ptr().read() };
        self.start = I::from_usize(start + 1);

        Some(ret)
    }
}

impl<E, B, I> core::iter::DoubleEndedIterator for IntoIterator<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        let start = self.start.to_usize();
        let end = self.end.to_usize();
        if start >= end {
            return None;
        }

        let end = end - 1;
        let ret = unsafe { self.buf.as_ref()[end].as_ptr().read() };
        self.end = I::from_usize(end);

        Some(ret)
    }
}

impl<E, B, I> core::iter::ExactSizeIterator for IntoIterator<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
}

impl<E, B, I> IntoIter for List<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    type Item = E;
    type IntoIter = IntoIterator<E, B, I>;

    fn into_iter(mut self) -> Self::IntoIter {
        let end = self.len;
        #[allow(clippy::uninit_assumed_init)]
        let buf = core::mem::replace(&mut self.buf, unsafe {
            // This is safe because we're going from MaybeUninit<[_]> to [MaybeUninit<_>]
            MaybeUninit::uninit().assume_init()
        });
        core::mem::forget(self);

        IntoIterator {
            start: I::from_usize(0),
            end,
            buf,
            elems: PhantomData,
        }
    }
}

impl<'a, E, B, I> IntoIter for &'a List<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    type Item = &'a E;
    type IntoIter = core::slice::Iter<'a, E>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

impl<'a, E, B, I> IntoIter for &'a mut List<E, B, I>
where
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    type Item = &'a mut E;
    type IntoIter = core::slice::IterMut<'a, E>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_mut_slice().iter_mut()
    }
}

#[cfg(feature = "nightly")]
pub type ArrayList<Element, const C: usize> = List<Element, [MaybeUninit<Element>; C], usize>;

#[cfg(feature = "nightly")]
pub type TiArrayList<Element, Index, const C: usize> =
    List<Element, [MaybeUninit<Element>; C], Index>;

#[cfg(feature = "nightly")]
impl<E, I, const C: usize> List<E, [MaybeUninit<E>; C], I>
where
    I: AsIndex,
{
    #[inline]
    pub fn new() -> Self {
        I::from_usize(C); // panics if I cannot index the whole array

        List {
            len: I::from_usize(0),
            buf: unsafe { MaybeUninit::uninit().assume_init() },
            elem: PhantomData,
        }
    }
}

#[cfg(feature = "nightly")]
impl<E, I, const C: usize> Default for List<E, [MaybeUninit<E>; C], I>
where
    I: AsIndex,
{
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "nightly")]
impl<E, I, const C: usize> core::clone::Clone for List<E, [MaybeUninit<E>; C], I>
where
    E: Clone,
    I: AsIndex,
{
    fn clone(&self) -> Self {
        let mut ret = Self::new();
        ret.clone_from(self);
        ret
    }

    fn clone_from(&mut self, source: &Self) {
        self.clear();
        for next in source {
            self.push(next.clone());
        }
    }
}

#[cfg(feature = "nightly")]
impl<E, I, const C: usize> From<&[E]> for List<E, [MaybeUninit<E>; C], I>
where
    E: Clone,
    I: AsIndex,
{
    fn from(source: &[E]) -> Self {
        if source.len() > C {
            panic!(
                "source should not have more than {} elements (has {})",
                C,
                source.len()
            );
        }

        let mut ret = Self::new();
        for next in source {
            ret.push(next.clone());
        }
        ret
    }
}

#[cfg(feature = "nightly")]
impl<E, I, const C: usize> From<&mut [E]> for List<E, [MaybeUninit<E>; C], I>
where
    E: Clone,
    I: AsIndex,
{
    fn from(source: &mut [E]) -> Self {
        if source.len() > C {
            panic!(
                "source should not have more than {} elements (has {})",
                C,
                source.len()
            );
        }

        let mut ret = Self::new();
        for next in source {
            ret.push(next.clone());
        }
        ret
    }
}

#[cfg(feature = "nightly")]
impl<V, E, B, I, const N: usize> core::cmp::PartialEq<List<E, B, I>> for [V; N]
where
    V: core::cmp::PartialEq<E>,
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    #[inline]
    fn eq(&self, other: &List<E, B, I>) -> bool {
        &self[..] == other.as_slice()
    }
}

#[cfg(feature = "nightly")]
impl<V, E, B, I, const N: usize> core::cmp::PartialEq<[V; N]> for List<E, B, I>
where
    E: core::cmp::PartialEq<V>,
    B: AsRef<[MaybeUninit<E>]> + AsMut<[MaybeUninit<E>]>,
    I: AsIndex,
{
    #[inline]
    fn eq(&self, other: &[V; N]) -> bool {
        self.as_slice() == &other[..]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::{size_of, size_of_val, MaybeUninit};

    #[test]
    fn it_works() {
        let mut backing = [MaybeUninit::uninit(); 256];
        {
            let tmp_list = List::<i32, _, usize>::from_buffer(&mut backing);
            assert_eq!(size_of_val(&tmp_list), 2 * size_of::<usize>())
        }
        {
            let tmp_list = List::<i32, _, usize>::from_buffer(&mut backing[..]);
            assert_eq!(size_of_val(&tmp_list), 3 * size_of::<usize>())
        }

        {
            let mut tmp_list = List::<i32, _, u64>::from_buffer(&mut backing[..]);
            tmp_list.push(123456789);

            // should be compiler error:
            // let test = tmp_list[0usize];
            assert_eq!(tmp_list[0u64], 123456789)
        }

        let mut list = List::<_, _, usize>::from_buffer(backing);
        list.push(1i32);
        list.push(2);
        list.push(3);

        assert_eq!(list[0], 1);
        assert_eq!(list.as_slice(), &[1, 2, 3]);
        assert_eq!(
            size_of_val(&list),
            size_of::<[i32; 256]>() + size_of::<usize>()
        );

        #[cfg(feature = "nightly")]
        {
            assert_eq!([1, 2, 3], list);
            assert_eq!(list, [1, 2, 3]);
            let _alias_test = ArrayList::<i32, 24>::new();
        }

        let mut it = (&list).into_iter();
        assert_eq!(it.next(), Some(&1));
        assert_eq!(it.next(), Some(&2));
        assert_eq!(it.next(), Some(&3));
        assert_eq!(it.next(), None);

        let mut it = list.into_iter().rev();
        assert_eq!(it.next(), Some(3));
        assert_eq!(it.next(), Some(2));
        assert_eq!(it.next(), Some(1));
        assert_eq!(it.next(), None);
    }
}
