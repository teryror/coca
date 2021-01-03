//! Traits providing genericity over storage strategies and index types.

use core::alloc::{Layout, LayoutError};
use core::convert::TryInto;
use core::marker::PhantomData;
use core::mem::MaybeUninit;

/// Two-way conversion between `Self` and `usize`.
///
/// # Safety
/// Implementors must ensure the conversion functions are each other's inverse,
/// i.e. `Capacity::from_usize(i).as_usize()` must either evaluate to `i`, or
/// panic for all `usize` values.
///
/// Using [`index_type!`] should be preferred over implementing this manually.
pub unsafe trait Capacity: Copy {
    /// Convert a `usize` into `Self`.
    fn from_usize(i: usize) -> Self;
    /// Convert `self` into `usize`.
    fn as_usize(&self) -> usize;
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
    panic!("called `as_usize` with value out of range")
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
    fn as_usize(&self) -> usize {
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
    fn as_usize(&self) -> usize {
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
    fn as_usize(&self) -> usize {
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
    fn as_usize(&self) -> usize {
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
    fn as_usize(&self) -> usize {
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
            fn as_usize(&self) -> usize {
                <$repr as $crate::storage::Capacity>::as_usize(&self.0)
            }
        }
    }
}

/// Types that specify a data structure's storage layout requirements.
pub trait LayoutSpec {
    /// Constructs a [`Layout`] for a memory block capable of holding the
    /// specified number of items.
    fn layout_with_capacity(items: usize) -> Result<Layout, LayoutError>;
}

/// Inconstructible type to mark data structures that require an array-like storage layout.
pub struct ArrayLike<T>(PhantomData<T>);
impl<T> LayoutSpec for ArrayLike<T> {
    fn layout_with_capacity(items: usize) -> Result<Layout, LayoutError> {
        Layout::array::<T>(items)
    }
}

/// An interface to a contiguous memory block for use by data structures.
pub unsafe trait Storage<R: LayoutSpec>: Sized {
    /// Extracts a pointer to the beginning of the memory block.
    ///
    /// # Safety
    /// Implementors must ensure the same pointer is returned everytime this
    /// method is called throughout the block's lifetime.
    fn get_ptr(&self) -> *const u8;
    /// Extracts a mutable pointer to the beginning of the memory block.
    ///
    /// # Safety
    /// Implementors must ensure the same pointer is returned everytime this
    /// method is called throughout the block's lifetime.
    fn get_mut_ptr(&mut self) -> *mut u8;
    /// Returns the maximum number of items the memory block can hold.
    ///
    /// # Safety
    /// What exactly constitutes an item depends on the argument type `R`.
    /// When called on a memory block with a layout matching
    /// `R::layout_with_capacity(n)`, this must return at most `n`.
    ///
    /// Implementors must ensure the same value is returned everytime this
    /// method is called throughout the block's lifetime.
    fn capacity(&self) -> usize;
}

#[inline(always)]
pub(crate) fn ptr_at_index<T, S: Storage<ArrayLike<T>>>(storage: &S, index: usize) -> *const T {
    debug_assert!(index <= storage.capacity());
    let ptr = storage.get_ptr() as *const T;
    ptr.wrapping_add(index)
}

#[inline(always)]
pub(crate) fn mut_ptr_at_index<T, S: Storage<ArrayLike<T>>>(
    storage: &mut S,
    index: usize,
) -> *mut T {
    debug_assert!(index <= storage.capacity());
    let ptr = storage.get_mut_ptr() as *mut T;
    ptr.wrapping_add(index)
}

/// Shorthand for `&'a mut [MaybeUninit<T>]` for use with generic data structures.
pub type SliceStorage<'a, T> = &'a mut [MaybeUninit<T>];
unsafe impl<T: Sized> Storage<ArrayLike<T>> for &mut [MaybeUninit<T>] {
    #[inline]
    fn get_ptr(&self) -> *const u8 {
        self.as_ptr() as *const u8
    }
    #[inline]
    fn get_mut_ptr(&mut self) -> *mut u8 {
        self.as_mut_ptr() as *mut u8
    }
    #[inline]
    fn capacity(&self) -> usize {
        self.len()
    }
}

/// Shorthand for [`coca::Box<'a, [MaybeUninit<T>]`](crate::arena::Box) for use
/// with generic data structures.
pub type ArenaStorage<'a, T> = crate::arena::Box<'a, [MaybeUninit<T>]>;
unsafe impl<T> Storage<ArrayLike<T>> for ArenaStorage<'_, T> {
    fn get_ptr(&self) -> *const u8 {
        self.as_ptr() as *const u8
    }
    fn get_mut_ptr(&mut self) -> *mut u8 {
        self.as_mut_ptr() as *mut u8
    }
    fn capacity(&self) -> usize {
        self.len()
    }
}

unsafe impl<R: LayoutSpec, S: Storage<R>> Storage<R> for crate::arena::Box<'_, S> {
    #[inline]
    fn get_ptr(&self) -> *const u8 {
        (**self).get_ptr()
    }
    #[inline]
    fn get_mut_ptr(&mut self) -> *mut u8 {
        (**self).get_mut_ptr()
    }
    #[inline]
    fn capacity(&self) -> usize {
        (**self).capacity()
    }
}

unsafe impl<R: LayoutSpec, S: Storage<R>> Storage<R> for &mut S {
    fn get_ptr(&self) -> *const u8 {
        (**self).get_ptr()
    }
    fn get_mut_ptr(&mut self) -> *mut u8 {
        (**self).get_mut_ptr()
    }
    fn capacity(&self) -> usize {
        (**self).capacity()
    }
}

/// Shorthand for [`alloc::Box<[MaybeUninit<T>]>`](alloc::boxed::Box) for use
/// with generic data structures.
#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub type HeapStorage<T> = alloc::boxed::Box<[MaybeUninit<T>]>;

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
unsafe impl<T> Storage<ArrayLike<T>> for HeapStorage<T> {
    fn get_ptr(&self) -> *const u8 {
        self.as_ptr() as *const u8
    }
    fn get_mut_ptr(&mut self) -> *mut u8 {
        self.as_mut_ptr() as *mut u8
    }
    fn capacity(&self) -> usize {
        self.len()
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
unsafe impl<R: LayoutSpec, S: Storage<R>> Storage<R> for alloc::boxed::Box<S> {
    fn get_ptr(&self) -> *const u8 {
        (**self).get_ptr()
    }
    fn get_mut_ptr(&mut self) -> *mut u8 {
        (**self).get_mut_ptr()
    }
    fn capacity(&self) -> usize {
        (**self).capacity()
    }
}

/// Shorthand for `[MaybeUninit<T>; C]` for use with generic data structures.
#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
pub type InlineStorage<T, const C: usize> = [MaybeUninit<T>; C];

#[cfg(feature = "nightly")]
#[cfg_attr(docs_rs, doc(cfg(feature = "nightly")))]
unsafe impl<T, const C: usize> Storage<ArrayLike<T>> for InlineStorage<T, C> {
    fn get_ptr(&self) -> *const u8 {
        self.as_ptr() as *const u8
    }
    fn get_mut_ptr(&mut self) -> *mut u8 {
        self.as_mut_ptr() as *mut u8
    }
    fn capacity(&self) -> usize {
        C
    }
}
