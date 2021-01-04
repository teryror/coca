//! Statically-sized containers for dynamically-sized types.
//!
//! This module uses unstable features and should be considered experimental.

use core::alloc::{Layout, LayoutError};
use core::fmt::{self, Debug, Formatter};
use core::marker::Unsize;
use core::mem::{align_of, size_of, ManuallyDrop, MaybeUninit};
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;

use crate::storage::{LayoutSpec, Storage};

/// The [`LayoutSpec`] for [`Object`] storage.
pub struct ObjectLayout(());
impl LayoutSpec for ObjectLayout {
    fn layout_with_capacity(bytes: usize) -> Result<Layout, LayoutError> {
        Layout::from_size_align(bytes, 8)
    }
}

/// Unit struct that can be used to modify the alignment of [`InlineStorage`].
#[repr(align(8))]
pub struct Align8;

/// Unit struct that can be used to modify the alignment of [`InlineStorage`].
#[repr(align(16))]
pub struct Align16;

/// Unit struct that can be used to modify the alignment of [`InlineStorage`].
#[repr(align(32))]
pub struct Align32;

/// Unit struct that can be used to modify the alignment of [`InlineStorage`].
#[repr(align(64))]
pub struct Align64;

/// Unit struct that can be used to modify the alignment of [`InlineStorage`].
#[repr(align(128))]
pub struct Align128;

/// An `N`-wide, partially initialized byte array with the alignment of `A`.
///
/// # Examples
/// Note that its size in memory is always a multiple of its alignment, so it
/// is recommended to chose `N` accordingly:
/// ```
/// use core::mem::{align_of, size_of};
/// use coca::object::{InlineStorage, Align16};
/// assert_eq!(align_of::<InlineStorage<Align16, 10>>(), 16);
///
/// assert_eq!(size_of::<InlineStorage<Align16, 10>>(), 16);
/// assert_eq!(size_of::<InlineStorage<Align16, 16>>(), 16);
/// assert_eq!(size_of::<InlineStorage<Align16, 20>>(), 32);
/// ```
#[repr(C)]
pub union InlineStorage<A, const N: usize> {
    force_alignment: ManuallyDrop<A>,
    data: [MaybeUninit<u8>; N],
}

unsafe impl<A, const N: usize> Storage<ObjectLayout> for InlineStorage<A, N> {
    fn capacity(&self) -> usize {
        N
    }
    fn get_ptr(&self) -> *const u8 {
        unsafe { self.data.as_ptr() as _ }
    }
    fn get_mut_ptr(&mut self) -> *mut u8 {
        unsafe { self.data.as_mut_ptr() as _ }
    }
}

/// A statically-sized container for dynamically-sized types.
///
/// This is primarily intended for use with `dyn Trait` (see
/// [`InlineObject::new`](Object::new) for example usage).
///
/// [`Vec`](crate::vec) should be preferred for dynamically sized arrays.
///
/// While it is *possible* to store a [`Sized`] type in an `Object`, there are
/// no benefits to doing so, and it adds at least one `usize` of storage overhead.
pub struct Object<T: ?Sized, S: Storage<ObjectLayout>> {
    meta: NonNull<T>,
    buf: S,
}

/// An object that stores dynamically-sized values in an inline array.
///
/// Note that this can only hold values with alignment less than or equal to 8.
/// If you need to store values with higher alignment requirements, use
/// [`InlineStorage`] explicitly; the required alignment can be specified with
/// the first generic type parameter (using [`Align16`], [`Align32`], etc.).
pub type InlineObject<T, const N: usize> = Object<T, InlineStorage<Align8, N>>;

impl<T: ?Sized, S: Storage<ObjectLayout>> Deref for Object<T, S> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        let dangling = self.meta.as_ptr() as *const T;
        let fat_ptr = dangling.set_ptr_value(self.buf.get_ptr());
        unsafe { fat_ptr.as_ref().unwrap() }
    }
}

impl<T: ?Sized, S: Storage<ObjectLayout>> DerefMut for Object<T, S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let dangling = self.meta.as_ptr() as *mut T;
        let fat_ptr = dangling.set_ptr_value(self.buf.get_mut_ptr());
        unsafe { fat_ptr.as_mut().unwrap() }
    }
}

impl<T: ?Sized + Debug, S: Storage<ObjectLayout>> Debug for Object<T, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T: ?Sized, S: Storage<ObjectLayout>> Drop for Object<T, S> {
    fn drop(&mut self) {
        unsafe { ((&mut **self) as *mut T).drop_in_place() };
    }
}

impl<T: ?Sized, A, const N: usize> Object<T, InlineStorage<A, N>> {
    #[inline]
    fn check_layout<U: Sized + Unsize<T>>() {
        #[inline(never)]
        #[cold]
        fn value_too_large(cap: usize, actual: usize) {
            panic!(
                "the object can only hold {} bytes, but the supplied value is {} bytes",
                cap, actual
            );
        }

        #[inline(never)]
        #[cold]
        fn value_too_strictly_aligned(guaranteed: usize, required: usize) {
            panic!("the object can only guarantee an alignment of {}, but the supplied value requires {}", guaranteed, required);
        }

        if size_of::<U>() > N {
            value_too_large(N, size_of::<U>())
        }
        if align_of::<U>() > align_of::<A>() {
            value_too_strictly_aligned(align_of::<A>(), align_of::<U>())
        }
    }

    /// Constructs a new inline object containing the provided value.
    ///
    /// # Panics
    /// Panics if `size_of::<U>()` is greater than the inline object's capacity,
    /// or if `align_of::<U>()` is greater than `align_of::<A>()`.
    ///
    /// # Examples
    /// ```
    /// use coca::InlineObject;
    ///
    /// trait Greeting { fn greet(&self) -> &'static str; }
    ///
    /// struct Sailors(u32);
    /// impl Greeting for Sailors {
    ///     fn greet(&self) -> &'static str {
    ///         if self.0 == 1 {
    ///             "Hello, Sailor!"
    ///         } else {
    ///             "Hello, Crew!"
    ///         }
    ///     }
    /// }
    ///
    /// struct World;
    /// impl Greeting for World {
    ///     fn greet(&self) -> &'static str {
    ///         "Hello, World!"
    ///     }
    /// }
    ///
    /// let mut obj: InlineObject<dyn Greeting, 4> = InlineObject::new(Sailors(1));
    /// assert_eq!(obj.greet(), "Hello, Sailor!");
    ///
    /// obj = InlineObject::new(World);
    /// assert_eq!(obj.greet(), "Hello, World!");
    /// ```
    pub fn new<U: Sized + Unsize<T>>(val: U) -> Self {
        Self::check_layout::<U>();
        let mut result = Object {
            meta: NonNull::<U>::dangling() as NonNull<T>,
            buf: InlineStorage {
                data: [MaybeUninit::uninit(); N],
            },
        };

        let ptr = result.buf.get_mut_ptr() as *mut U;
        unsafe { ptr.write(val) };

        result
    }

    /// Drops the value currently held by the object and stores the provided value.
    ///
    /// # Panics
    /// Panics if `size_of::<U>()` is greater than the inline object's capacity,
    /// or if `align_of::<U>()` is greater than `align_of::<A>()`.
    ///
    /// # Examples
    /// ```
    /// use coca::InlineObject;
    /// let mut obj: InlineObject<[i32], 16> = InlineObject::new([1, 2, 3]);
    /// assert_eq!(*obj, [1, 2, 3]);
    ///
    /// obj.set([4, 5, 6, 7]);
    /// assert_eq!(*obj, [4, 5, 6, 7]);
    /// ```
    pub fn set<U: Sized + Unsize<T>>(&mut self, val: U) {
        Self::check_layout::<U>();
        unsafe { ((&mut **self) as *mut T).drop_in_place() };

        self.meta = NonNull::<U>::dangling() as NonNull<T>;
        let ptr = self.buf.get_mut_ptr() as *mut U;
        unsafe { ptr.write(val) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::align_of;

    #[test]
    fn inline_storage_layout() {
        fn test_layout<A, const B: usize>(align: usize) {
            assert_eq!(align_of::<A>(), align);
            assert_eq!(align_of::<InlineStorage<A, B>>(), align);

            let expected_size = (B + (align - 1)) & !(align - 1);
            assert_eq!(size_of::<InlineStorage<A, B>>(), expected_size);
        }

        test_layout::<Align8, 5>(8);
        test_layout::<Align8, 13>(8);
        test_layout::<Align8, 17>(8);

        test_layout::<Align16, 1>(16);
        test_layout::<Align16, 39>(16);

        test_layout::<Align32, 20>(32);
        test_layout::<Align32, 101>(32);

        test_layout::<Align64, 40>(64);
        test_layout::<Align64, 80>(64);

        test_layout::<Align128, 50>(128);
        test_layout::<Align128, 150>(128);
    }

    #[test]
    fn drops_correctly() {
        use core::cell::Cell;

        #[derive(Debug)]
        struct Droppable<'a> {
            drop_count: &'a Cell<u32>,
        }

        impl Drop for Droppable<'_> {
            fn drop(&mut self) {
                let c = self.drop_count.get();
                self.drop_count.set(c + 1);
            }
        }

        let drop_count = Cell::new(0);
        {
            let mut obj: InlineObject<dyn Debug, 8> = InlineObject::new(Droppable {
                drop_count: &drop_count,
            });

            obj.set(Droppable {
                drop_count: &drop_count,
            });
            assert_eq!(drop_count.get(), 1);
        }
        assert_eq!(drop_count.get(), 2);
    }
}
