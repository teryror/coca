//! Traits providing genericity over storage strategies and index types.

use core::convert::TryInto;
use core::mem::MaybeUninit;

/// Two-way conversion between `Self` and `usize`.
///
/// # Safety
/// Implementors must ensure the conversion functions are each other's inverse,
/// i.e. `Capacity::from_usize(i).into_usize()` must either evaluate to `i`, or
/// panic for all `usize` values.
///
/// Using [`index_type!`] should be preferred over implementing this manually.
pub unsafe trait Capacity: Copy {
    /// Convert a `usize` into `Self`.
    fn from_usize(i: usize) -> Self;
    /// Convert `self` into `usize`.
    fn into_usize(&self) -> usize;
}

#[inline(never)]
#[cold]
#[track_caller]
fn from_value_out_of_range(i: usize) -> ! {
    panic!("called `from_usize` with value out of range (is {})", i)
}

#[inline(never)]
#[cold]
#[track_caller]
fn into_value_out_of_range() -> ! {
    panic!("called `into_usize` with value out of range")
}

unsafe impl Capacity for u8 {
    #[inline]
    #[track_caller]
    fn from_usize(i: usize) -> Self {
        if let Ok(t) = i.try_into() {
            t
        } else {
            from_value_out_of_range(i);
        }
    }

    #[inline]
    fn into_usize(&self) -> usize {
        (*self).into()
    }
}

unsafe impl Capacity for u16 {
    #[inline]
    #[track_caller]
    fn from_usize(i: usize) -> Self {
        if let Ok(t) = i.try_into() {
            t
        } else {
            from_value_out_of_range(i);
        }
    }

    #[inline]
    fn into_usize(&self) -> usize {
        (*self).into()
    }
}

unsafe impl Capacity for u32 {
    #[inline]
    #[track_caller]
    fn from_usize(i: usize) -> Self {
        if let Ok(t) = i.try_into() {
            t
        } else {
            from_value_out_of_range(i);
        }
    }

    #[inline]
    #[track_caller]
    fn into_usize(&self) -> usize {
        if let Ok(t) = (*self).try_into() {
            t
        } else {
            into_value_out_of_range();
        }
    }
}

unsafe impl Capacity for u64 {
    #[inline]
    #[track_caller]
    fn from_usize(i: usize) -> Self {
        if let Ok(t) = i.try_into() {
            t
        } else {
            from_value_out_of_range(i);
        }
    }

    #[inline]
    #[track_caller]
    fn into_usize(&self) -> usize {
        if let Ok(t) = (*self).try_into() {
            t
        } else {
            into_value_out_of_range();
        }
    }
}

unsafe impl Capacity for usize {
    #[inline]
    fn from_usize(i: usize) -> Self {
        i
    }

    #[inline]
    fn into_usize(&self) -> usize {
        *self
    }
}

/// Generates a newtype wrapping an implementor of [`Capacity`].
///
/// This can help in avoiding use of the wrong index with a [`Vec`](crate::vec::Vec).
///
/// # Examples
/// ```compile_fail
/// use coca::{index_type, Vec};
/// use core::mem::MaybeUninit;
///
/// index_type! { pub IndexA: u8 };
/// index_type! { IndexB: u8 };
///
/// let mut backing_a = [MaybeUninit::<u32>::uninit(); 20];
/// let mut backing_b = [MaybeUninit::<u32>::uninit(); 30];
///
/// let mut vec_a = Vec::<_, _, IndexA>::from(&mut backing_a[..]);
/// for i in 0..20 { vec_a.push(i); }
///
/// let mut vec_b = Vec::<_, _, IndexB>::from(&mut backing_b[..]);
/// for i in 0..30 { vec_b.push(i * 2); }
///
/// let a = vec_a[IndexA(10)];
/// let b = vec_b[IndexB(15)];
/// let c = vec_a[IndexB(25)];
/// //      ^^^^^^^^^^^^^^^^^ `coca::Vec<...>` cannot be indexed by `IndexB`
/// ```
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

        unsafe impl $crate::storage::Capacity for $name {
            #[inline]
            #[track_caller]
            fn from_usize(i: usize) -> Self {
                Self(<$repr as $crate::storage::Capacity>::from_usize(i))
            }

            #[inline]
            #[track_caller]
            fn into_usize(&self) -> usize {
                <$repr as $crate::storage::Capacity>::into_usize(&self.0)
            }
        }
    }
}

/// An interface for a contiguous memory block for use by data structures.
pub unsafe trait ContiguousStorage<T>: Sized
where
    T: Sized,
{
    /// Extracts a slice over the entire memory block.
    ///
    /// # Safety
    /// Implementors must ensure the length of the returned slice never changes.
    fn storage(&self) -> &[MaybeUninit<T>];
    /// Extracts a mutable slice over the entire memory block.
    ///
    /// # Safety
    /// Implementors must ensure the length of the returned slice never changes.
    fn storage_mut(&mut self) -> &mut [MaybeUninit<T>];

    /// Returns the size of the memory block in units of T.
    #[inline]
    fn capacity(&self) -> usize {
        self.storage().len()
    }

    /// Returns a pointer to the element at position `index`.
    ///
    /// # Safety
    /// The resulting pointer does not need to be in bounds but it is potentially
    /// hazardous to dereference (which requires `unsafe`).
    ///
    /// Even when in bounds, the value it points to may not be initialized.
    #[inline]
    fn get_ptr(&self, index: usize) -> *const T {
        debug_assert!(index <= self.storage().len());
        self.storage().as_ptr().wrapping_add(index) as _
    }

    /// Returns a mutable pointer to the element at position `index`.
    ///
    /// # Safety
    /// The resulting pointer does not need to be in bounds but it is potentially
    /// hazardous to dereference (which requires `unsafe`).
    ///
    /// Even when in bounds, the value it points to may not be initialized.
    #[inline]
    fn get_mut_ptr(&mut self, index: usize) -> *mut T {
        debug_assert!(index <= self.storage_mut().len());
        self.storage_mut().as_mut_ptr().wrapping_add(index) as _
    }
}

/// Shorthand for `&'a mut [MaybeUninit<T>]` for use with generic data structures.
pub type SliceStorage<'a, T> = &'a mut [MaybeUninit<T>];
unsafe impl<T: Sized> ContiguousStorage<T> for SliceStorage<'_, T> {
    #[inline]
    fn storage(&self) -> &[MaybeUninit<T>] {
        &self[..]
    }
    #[inline]
    fn storage_mut(&mut self) -> &mut [MaybeUninit<T>] {
        self
    }
}

/// Shorthand for [`coca::Box<'a, [MaybeUninit<T>]`](crate::arena::Box) for use
/// with generic data structures.
pub type ArenaStorage<'a, T> = crate::arena::Box<'a, [MaybeUninit<T>]>;
unsafe impl<T> ContiguousStorage<T> for ArenaStorage<'_, T> {
    #[inline]
    fn storage(&self) -> &[MaybeUninit<T>] {
        self
    }
    #[inline]
    fn storage_mut(&mut self) -> &mut [MaybeUninit<T>] {
        self
    }
}

/// Shorthand for [`alloc::Box<[MaybeUninit<T>]>`](alloc::boxed::Box) for use
/// with generic data structures.
#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub type HeapStorage<T> = alloc::boxed::Box<[MaybeUninit<T>]>;

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
unsafe impl<T> ContiguousStorage<T> for HeapStorage<T> {
    #[inline]
    fn storage(&self) -> &[MaybeUninit<T>] {
        self
    }
    #[inline]
    fn storage_mut(&mut self) -> &mut [MaybeUninit<T>] {
        self
    }
}

/// Shorthand for `[MaybeUninit<T>; C]` for use with generic data structures.
#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
pub type InlineStorage<T, const C: usize> = [MaybeUninit<T>; C];

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
unsafe impl<T, const C: usize> ContiguousStorage<T> for InlineStorage<T, C> {
    #[inline]
    fn storage(&self) -> &[MaybeUninit<T>] {
        &self[..]
    }
    #[inline]
    fn storage_mut(&mut self) -> &mut [MaybeUninit<T>] {
        &mut self[..]
    }
}

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
unsafe impl<'a, T, const C: usize> ContiguousStorage<T> for &'a mut [MaybeUninit<T>; C] {
    #[inline]
    fn storage(&self) -> &[MaybeUninit<T>] {
        &self[..]
    }
    #[inline]
    fn storage_mut(&mut self) -> &mut [MaybeUninit<T>] {
        &mut self[..]
    }
    #[inline]
    fn capacity(&self) -> usize {
        C
    }
}

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
unsafe impl<'a, T, const C: usize> ContiguousStorage<T> for crate::Box<'a, [MaybeUninit<T>; C]> {
    #[inline]
    fn storage(&self) -> &[MaybeUninit<T>] {
        &self[..]
    }
    #[inline]
    fn storage_mut(&mut self) -> &mut [MaybeUninit<T>] {
        &mut self[..]
    }
    #[inline]
    fn capacity(&self) -> usize {
        C
    }
}
#[cfg(all(feature = "nightly", feature = "alloc"))]
#[cfg_attr(docs_rs, doc(cfg(all(feature = "alloc", feature = "nightly"))))]
unsafe impl<'a, T, const C: usize> ContiguousStorage<T> for alloc::boxed::Box<[MaybeUninit<T>; C]> {
    #[inline]
    fn storage(&self) -> &[MaybeUninit<T>] {
        &self[..]
    }
    #[inline]
    fn storage_mut(&mut self) -> &mut [MaybeUninit<T>] {
        &mut self[..]
    }
    #[inline]
    fn capacity(&self) -> usize {
        C
    }
}
