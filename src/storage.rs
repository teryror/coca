//! Traits abstracting over storage strategies and index types.

use core::alloc::{Layout, LayoutError};
use core::convert::{TryFrom, TryInto};
use core::fmt::Debug;
use core::hash::Hash;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ops::{Range, RangeBounds};
use core::ptr::NonNull;

/// Types that can be used for indexing into array-like data structures.
///
/// # Safety
/// Implementors must ensure that `Capacity::from_usize(i).as_usize() == i` for
/// all values `i <= MAX_REPRESENTABLE`. Otherwise, this expression must panic
/// or evaluate to `false`.
///
/// Using [`index_type!`] should be preferred over implementing this manually.
pub unsafe trait Capacity: Copy + Debug + Eq + Hash + Ord {
    /// The maximum `usize` value that can safely be represented by this type.
    const MAX_REPRESENTABLE: usize;
    /// Convert a `usize` into `Self`.
    fn from_usize(i: usize) -> Self;
    /// Convert `self` into `usize`.
    fn as_usize(&self) -> usize;
}

#[cold]
#[inline(never)]
#[track_caller]
pub(crate) fn buffer_too_large_for_index_type<I: Capacity>() {
    panic!(
        "provided storage block cannot be fully indexed by type {}",
        core::any::type_name::<I>()
    );
}

pub(crate) fn normalize_range<I: Capacity, R: RangeBounds<I>>(range: R, max_end: usize) -> Range<usize> {
    use core::ops::Bound;
    let start = match range.start_bound() {
        Bound::Included(x) => x.as_usize(),
        Bound::Excluded(x) => x.as_usize().saturating_add(1),
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(x) => x.as_usize().saturating_add(1),
        Bound::Excluded(x) => x.as_usize(),
        Bound::Unbounded => max_end,
    };

    assert!(end <= max_end, "invalid range specifier: end (is {:?}) is greater than {:?}", end, max_end);
    assert!(start <= end, "invalid range specifier: start (is {:?}) is greater than end (is {:?})", start, end);

    Range { start, end }
}

#[allow(clippy::cast_possible_truncation)]
unsafe impl Capacity for u8 {
    const MAX_REPRESENTABLE: usize = 0xFF;
    #[inline]
    fn from_usize(i: usize) -> Self {
        debug_assert!(<usize as TryInto<Self>>::try_into(i).is_ok());
        i as u8
    }

    #[inline]
    fn as_usize(&self) -> usize {
        *self as usize
    }
}

#[allow(clippy::cast_possible_truncation)]
unsafe impl Capacity for u16 {
    const MAX_REPRESENTABLE: usize = 0xFFFF;
    #[inline]
    fn from_usize(i: usize) -> Self {
        debug_assert!(<usize as TryInto<Self>>::try_into(i).is_ok());
        i as u16
    }

    #[inline]
    fn as_usize(&self) -> usize {
        *self as usize
    }
}

#[allow(clippy::cast_possible_truncation)]
unsafe impl Capacity for u32 {
    const MAX_REPRESENTABLE: usize = 0xFFFF_FFFF;
    #[inline]
    fn from_usize(i: usize) -> Self {
        debug_assert!(<usize as TryInto<Self>>::try_into(i).is_ok());
        i as u32
    }

    #[inline]
    fn as_usize(&self) -> usize {
        debug_assert!(<usize as TryFrom<Self>>::try_from(*self).is_ok());
        *self as usize
    }
}

#[allow(clippy::cast_possible_truncation)]
unsafe impl Capacity for u64 {
    const MAX_REPRESENTABLE: usize = usize::max_value();
    #[inline]
    fn from_usize(i: usize) -> Self {
        debug_assert!(<usize as TryInto<Self>>::try_into(i).is_ok());
        i as u64
    }

    #[inline]
    fn as_usize(&self) -> usize {
        debug_assert!(<usize as TryFrom<Self>>::try_from(*self).is_ok());
        *self as usize
    }
}

unsafe impl Capacity for usize {
    const MAX_REPRESENTABLE: usize = usize::max_value();
    #[inline]
    fn from_usize(i: usize) -> Self {
        i
    }

    #[inline]
    fn as_usize(&self) -> usize {
        *self
    }
}

/// Generates one or more new types wrapping an implementor of [`Capacity`].
///
/// This can help in avoiding use of the wrong index with a [`Vec`](crate::collections::vec::Vec).
///
/// # Examples
/// ```compile_fail
/// use coca::{index_type, vec::Vec};
/// use core::mem::MaybeUninit;
///
/// index_type! {
///     pub IndexA: u8;
///     IndexB: u8;
/// };
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
    ( $(#[$attrs:meta])* $v:vis $name:ident: $repr:ty ) => {
        $(#[$attrs])*
        #[derive(
            core::marker::Copy,
            core::clone::Clone,
            core::default::Default,
            core::fmt::Debug,
            core::hash::Hash,
            core::cmp::PartialEq,
            core::cmp::Eq,
            core::cmp::PartialOrd,
            core::cmp::Ord)]
        $v struct $name($repr);

        unsafe impl $crate::storage::Capacity for $name {
            const MAX_REPRESENTABLE: usize = <$repr as $crate::storage::Capacity>::MAX_REPRESENTABLE;
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
    };

    ( $(#[$attrs:meta])* $v:vis $name:ident: $repr:ty ; $($rest:tt)* ) => {
        $crate::index_type!($(#[$attrs])* $v $name: $repr);
        $crate::index_type!($($rest)*);
    };

    () => {}
}

/// Types that specify a data structure's storage layout requirements.
pub trait LayoutSpec {
    /// Constructs a [`Layout`] for a memory block capable of holding the
    /// specified number of items.
    fn layout_with_capacity(items: usize) -> Result<Layout, LayoutError>;
}

/// Inconstructible type to mark data structures that require an array-like storage layout.
pub struct ArrayLayout<T>(PhantomData<T>);
impl<T> LayoutSpec for ArrayLayout<T> {
    fn layout_with_capacity(items: usize) -> Result<Layout, LayoutError> {
        Layout::array::<T>(items)
    }
}

/// An interface to a contiguous memory block for use by data structures.
#[allow(clippy::missing_safety_doc)] // individual methods _do_ have safety docs!
pub unsafe trait Storage<R: LayoutSpec>: Sized {
    /// Extracts a pointer to the beginning of the memory block.
    ///
    /// # Safety
    /// Implementors must ensure the same pointer is returned every time this
    /// method is called throughout the block's lifetime.
    fn get_ptr(&self) -> *const u8;
    /// Extracts a mutable pointer to the beginning of the memory block.
    ///
    /// # Safety
    /// Implementors must ensure the same pointer is returned every time this
    /// method is called throughout the block's lifetime.
    fn get_mut_ptr(&mut self) -> *mut u8;
    /// Returns the maximum number of items the memory block can hold.
    ///
    /// # Safety
    /// What exactly constitutes an item depends on the argument type `R`.
    /// When called on a memory block with a layout matching
    /// `R::layout_with_capacity(n)`, this must return at most `n`.
    ///
    /// Implementors must ensure the same value is returned every time this
    /// method is called throughout the block's lifetime.
    fn capacity(&self) -> usize;
}

#[inline(always)]
pub(crate) fn ptr_at_index<T, S: Storage<ArrayLayout<T>>>(storage: &S, index: usize) -> *const T {
    debug_assert!(index <= storage.capacity());
    let ptr = storage.get_ptr().cast::<T>();
    ptr.wrapping_add(index)
}

#[inline(always)]
pub(crate) fn mut_ptr_at_index<T, S: Storage<ArrayLayout<T>>>(
    storage: &mut S,
    index: usize,
) -> *mut T {
    debug_assert!(index <= storage.capacity());
    let ptr = storage.get_mut_ptr().cast::<T>();
    ptr.wrapping_add(index)
}

/// Shorthand for `&'a mut [MaybeUninit<T>]` for use with generic data structures.
pub type SliceStorage<'a, T> = &'a mut [MaybeUninit<T>];
unsafe impl<T: Sized> Storage<ArrayLayout<T>> for &mut [MaybeUninit<T>] {
    #[inline]
    fn get_ptr(&self) -> *const u8 {
        self.as_ptr().cast()
    }
    #[inline]
    fn get_mut_ptr(&mut self) -> *mut u8 {
        self.as_mut_ptr().cast()
    }
    #[inline]
    fn capacity(&self) -> usize {
        self.len()
    }
}

/// A fat pointer to an arena-allocated storage block conforming to a [`LayoutSpec`].
pub struct ArenaStorage<'src, R: LayoutSpec> {
    ptr: NonNull<u8>,
    cap: usize,
    spec: PhantomData<R>,
    src: PhantomData<&'src ()>,
}

impl<R: LayoutSpec> ArenaStorage<'_, R> {
    pub(crate) unsafe fn from_raw_parts(ptr: *mut u8, cap: usize) -> Option<Self> {
        let ptr = NonNull::new(ptr)?;
        Some(ArenaStorage {
            ptr,
            cap,
            spec: PhantomData,
            src: PhantomData,
        })
    }
}

unsafe impl<R: LayoutSpec> Storage<R> for ArenaStorage<'_, R> {
    fn get_ptr(&self) -> *const u8 {
        self.ptr.as_ptr() as _
    }

    fn get_mut_ptr(&mut self) -> *mut u8 {
        self.ptr.as_ptr()
    }

    fn capacity(&self) -> usize {
        self.cap
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

/// A fat pointer to a heap-allocated storage block conforming to a [`LayoutSpec`].
#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub struct AllocStorage<R: LayoutSpec> {
    ptr: NonNull<u8>,
    cap: usize,
    spec: PhantomData<R>,
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<R: LayoutSpec> AllocStorage<R> {
    /// Allocates a new storage block with the specified capacity with the
    /// global allocator.
    ///
    /// # Panics
    /// Panics if `capacity` is large enough to cause a layout error, or if
    /// allocation fails.
    pub fn with_capacity(capacity: usize) -> Self {
        let layout =
            R::layout_with_capacity(capacity).expect("layout error in AllocStorage::with_capacity");
        let ptr = unsafe { alloc::alloc::alloc(layout) };
        let ptr = NonNull::new(ptr).expect("allocation failure in AllocStorage::with_capacity");
        AllocStorage {
            ptr,
            cap: capacity,
            spec: PhantomData,
        }
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<R: LayoutSpec> Drop for AllocStorage<R> {
    fn drop(&mut self) {
        let layout = R::layout_with_capacity(self.cap).expect("dropped an invalid AllocStorage");
        unsafe { alloc::alloc::dealloc(self.ptr.as_ptr(), layout) };
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
unsafe impl<R: LayoutSpec> Storage<R> for AllocStorage<R> {
    fn get_ptr(&self) -> *const u8 {
        self.ptr.as_ptr() as _
    }
    fn get_mut_ptr(&mut self) -> *mut u8 {
        self.ptr.as_ptr()
    }
    fn capacity(&self) -> usize {
        self.cap
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
pub type InlineStorage<T, const C: usize> = [MaybeUninit<T>; C];

unsafe impl<T, const C: usize> Storage<ArrayLayout<T>> for InlineStorage<T, C> {
    fn get_ptr(&self) -> *const u8 {
        self.as_ptr().cast()
    }
    fn get_mut_ptr(&mut self) -> *mut u8 {
        self.as_mut_ptr().cast()
    }
    fn capacity(&self) -> usize {
        C
    }
}
