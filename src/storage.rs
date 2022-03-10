//! Traits abstracting over storage strategies and index types.

use core::alloc::{Layout, LayoutError};
use core::convert::{TryFrom, TryInto};
use core::fmt::Debug;
use core::hash::Hash;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ops::{Range, RangeBounds};
use core::ptr::NonNull;

use crate::CapacityError;

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
    /// The zero value for this type.
    const ZERO: Self;
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

#[cold]
#[inline(never)]
#[track_caller]
pub(crate) fn usize_exceeds_max_capacity<I: Capacity>() {
    panic!(
        "maximum capacity of index type {} exceeds the requested capacity",
        core::any::type_name::<I>()
    );
}

#[inline]
pub(crate) fn cast_capacity<I: Capacity>(capacity: usize) -> I {
    if capacity > I::MAX_REPRESENTABLE {
        usize_exceeds_max_capacity::<I>();
    }
    I::from_usize(capacity)
}

pub(crate) fn normalize_range<I: Capacity, R: RangeBounds<I>>(
    range: R,
    max_end: usize,
) -> Range<usize> {
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

    assert!(
        end <= max_end,
        "invalid range specifier: end (is {:?}) is greater than {:?}",
        end,
        max_end
    );
    assert!(
        start <= end,
        "invalid range specifier: start (is {:?}) is greater than end (is {:?})",
        start,
        end
    );

    Range { start, end }
}

#[allow(clippy::cast_possible_truncation)]
unsafe impl Capacity for u8 {
    const MAX_REPRESENTABLE: usize = 0xFF;
    const ZERO: Self = 0u8;
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
    const ZERO: Self = 0u16;
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
    const ZERO: Self = 0u32;
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
    const ZERO: Self = 0u64;
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
    const ZERO: Self = 0usize;
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
            const ZERO: Self = Self(<$repr as $crate::storage::Capacity>::ZERO);
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
    /// A type representing the approximate size of a single item.
    type Item: Sized;

    /// Constructs a [`Layout`] for a memory block capable of holding the
    /// specified number of items.
    fn layout_with_capacity(items: usize) -> Result<Layout, LayoutError>;
}

/// Inconstructible type to mark data structures that require an array-like storage layout.
pub struct ArrayLayout<T>(PhantomData<T>);
impl<T> LayoutSpec for ArrayLayout<T> {
    type Item = T;

    fn layout_with_capacity(items: usize) -> Result<Layout, LayoutError> {
        Layout::array::<T>(items)
    }
}

/// An interface to a contiguous memory block for use by data structures.
#[allow(clippy::missing_safety_doc)] // individual methods _do_ have safety docs!
pub unsafe trait Storage<R: LayoutSpec>: Sized {
    /// The minimum capacity which must be indexable for this storage type.
    const MIN_REPRESENTABLE: usize = 0;
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
    /// Try to grow a storage instance, reallocating when supported.
    ///
    /// # Safety
    /// When supported, this method must return a new, non-overlapping
    /// memory block without invalidating the current block.
    fn try_grow<I: Capacity>(
        &mut self,
        _min_capacity: Option<usize>,
    ) -> Result<Self, CapacityError> {
        CapacityError::new()
    }
}

/// An interface for storage types which are owned, not bound to an external buffer.
pub trait OwnedStorage<R: LayoutSpec>: Storage<R> {
    /// Create a new storage buffer with a minimum capacity.
    fn try_with_capacity(min_capacity: usize) -> Result<Self, CapacityError>;
}

/// An interface for storage types which have a default initializer.
pub trait DefaultStorage<R: LayoutSpec>: OwnedStorage<R> {
    /// An empty instance of the Storage.
    const UNINIT: Self;
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
    const MIN_REPRESENTABLE: usize = S::MIN_REPRESENTABLE;

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
    const MIN_REPRESENTABLE: usize = S::MIN_REPRESENTABLE;

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

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
/// Policy for heap storage (re)allocation.
pub unsafe trait AllocPolicy {
    #[inline]
    // FIXME add exact: bool parameter?
    /// Try to grow an existing allocation.
    fn try_grow<R: LayoutSpec, I: Capacity>(
        _from_capacity: usize,
        _min_capacity: Option<usize>,
    ) -> Result<(NonNull<u8>, usize), CapacityError> {
        CapacityError::new()
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
/// An allocation policy for constant capacity storage.
pub struct NoResize;

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
unsafe impl AllocPolicy for NoResize {}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
/// An allocation policy using exponential growth.
pub struct ExpGrow;

#[cfg(feature = "alloc")]
const fn min_non_zero_cap<T>() -> usize {
    if core::mem::size_of::<T>() == 1 {
        8
    } else if core::mem::size_of::<T>() <= 1024 {
        4
    } else {
        1
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
unsafe impl AllocPolicy for ExpGrow {
    #[inline]
    fn try_grow<R: LayoutSpec, I: Capacity>(
        from_capacity: usize,
        min_capacity: Option<usize>,
    ) -> Result<(NonNull<u8>, usize), CapacityError> {
        let min_cap = min_capacity.unwrap_or(0).max(min_non_zero_cap::<R::Item>());
        let cap = min_cap.max((from_capacity.saturating_mul(2)).min(I::MAX_REPRESENTABLE));
        if cap <= from_capacity || cap < min_cap {
            return CapacityError::new();
        }

        let layout = R::layout_with_capacity(cap).expect("realloc to invalid AllocStorage");
        let ptr = unsafe { alloc::alloc::alloc(layout) };
        NonNull::new(ptr).map(|ptr| (ptr, cap)).ok_or(CapacityError)
    }
}

/// A fat pointer to a heap-allocated storage block conforming to a [`LayoutSpec`].
#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
pub struct AllocStorage<R: LayoutSpec, A: AllocPolicy = NoResize> {
    ptr: NonNull<u8>,
    cap: usize,
    spec: PhantomData<(R, A)>,
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<R: LayoutSpec, A: AllocPolicy> AllocStorage<R, A> {
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
impl<R: LayoutSpec, A: AllocPolicy> Drop for AllocStorage<R, A> {
    fn drop(&mut self) {
        if self.cap != 0 {
            let layout =
                R::layout_with_capacity(self.cap).expect("dropped an invalid AllocStorage");
            unsafe { alloc::alloc::dealloc(self.ptr.as_ptr(), layout) };
        }
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
unsafe impl<R: LayoutSpec, A: AllocPolicy> Storage<R> for AllocStorage<R, A> {
    fn get_ptr(&self) -> *const u8 {
        self.ptr.as_ptr() as _
    }
    fn get_mut_ptr(&mut self) -> *mut u8 {
        self.ptr.as_ptr()
    }
    fn capacity(&self) -> usize {
        self.cap
    }
    fn try_grow<I: Capacity>(
        &mut self,
        min_capacity: Option<usize>,
    ) -> Result<Self, CapacityError> {
        let (ptr, cap) = A::try_grow::<R, I>(self.cap, min_capacity)?;
        Ok(AllocStorage {
            ptr,
            cap,
            spec: PhantomData,
        })
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<R: LayoutSpec, A: AllocPolicy> OwnedStorage<R> for AllocStorage<R, A> {
    #[inline]
    fn try_with_capacity(min_capacity: usize) -> Result<Self, CapacityError> {
        Ok(Self::with_capacity(min_capacity))
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<R: LayoutSpec, A: AllocPolicy + Default> DefaultStorage<R> for AllocStorage<R, A> {
    const UNINIT: Self = AllocStorage {
        ptr: NonNull::dangling(),
        cap: 0,
        spec: PhantomData,
    };
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
/// Alias for a reallocating Storage type with the default behavior.
pub type ReallocStorage<R> = AllocStorage<R, ExpGrow>;

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
    const MIN_REPRESENTABLE: usize = C;
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

impl<T, const C: usize> OwnedStorage<ArrayLayout<T>> for InlineStorage<T, C> {
    #[inline]
    fn try_with_capacity(min_capacity: usize) -> Result<Self, CapacityError> {
        if min_capacity > C {
            CapacityError::new()
        } else {
            unsafe { MaybeUninit::uninit().assume_init() }
        }
    }
}

impl<T, const C: usize> DefaultStorage<ArrayLayout<T>> for InlineStorage<T, C> {
    const UNINIT: Self = unsafe { MaybeUninit::uninit().assume_init() };
}
