//! Arena-based memory management.
//!
//! An arena controls a contiguous region of memory, partitioning it by simply
//! incrementing a pointer. Once such an allocation goes out of scope, the
//! memory cannot be reclaimed until the entire region is cleared in aggregate.
//! This scheme has minimal runtime overhead, at the cost of potential memory
//! fragmentation.
//!
//! In order to optimally utilize the borrow checker, [`Arena`] does not have
//! a `clear` method. Instead, the underlying region is reset by dropping
//! the arena, and may safely be freed or reused; a [`Box<'src, T>`] cannot
//! outlive the arena it was allocated from.
//!
//! On the flip-side, an arena must live as long as the longest-living value
//! inside it, leaving the remainder of the region unusable. To mitigate this,
//! one can [construct an arena from an existing one](Arena::make_sub_arena),
//! which will manage the remaining memory. It's not possible to allocate out
//! of the original arena as long as such a sub-arena lives (though all previously
//! allocated values remain accessible), resulting in stack-like behavior.

use crate::list::{AsIndex, BoxArrayList, BoxSliceList, List};

use core::alloc::Layout;
use core::cmp::Ordering;
use core::fmt::{self, Debug, Display, Formatter, Pointer, Write};
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut, Range};
use core::ptr::{null_mut, NonNull};
use core::slice::from_raw_parts_mut;

/// A pointer type providing ownership of an arena allocation.
///
/// While the owned value will be dropped as normal, no additional overhead
/// for memory management is incurred.
///
/// See the [module-level documentation](crate::arena) for more.
pub struct Box<'src, T: ?Sized> {
    ptr: NonNull<T>,
    val: PhantomData<T>,        // Indicates this is an owning pointer
    src: PhantomData<&'src ()>, // Indicates this pointer must not outlive 'src
}

impl<T: ?Sized> Deref for Box<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T: ?Sized> DerefMut for Box<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T: ?Sized> AsRef<T> for Box<'_, T> {
    fn as_ref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T: ?Sized> AsMut<T> for Box<'_, T> {
    fn as_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

#[cfg(feature = "nightly")]
impl<T, const N: usize> AsRef<[T]> for Box<'_, [T; N]> {
    fn as_ref(&self) -> &[T] {
        &self[..]
    }
}

#[cfg(feature = "nightly")]
impl<T, const N: usize> AsMut<[T]> for Box<'_, [T; N]> {
    fn as_mut(&mut self) -> &mut [T] {
        &mut self[..]
    }
}

impl<T: ?Sized> Drop for Box<'_, T> {
    fn drop(&mut self) {
        // TODO: Verify that calls to this function are optimized out when T: !Drop
        unsafe { self.ptr.as_ptr().drop_in_place() }
    }
}

impl<T: Debug + ?Sized> Debug for Box<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&**self, f)
    }
}

impl<T: Display + ?Sized> Display for Box<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&**self, f)
    }
}

impl<T: ?Sized> Pointer for Box<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Pointer::fmt(&self.ptr, f)
    }
}

impl<T: ?Sized + PartialEq> PartialEq for Box<'_, T> {
    #[inline]
    fn eq(&self, other: &Box<'_, T>) -> bool {
        PartialEq::eq(&**self, &**other)
    }
}
impl<T: ?Sized + PartialOrd> PartialOrd for Box<'_, T> {
    #[inline]
    fn partial_cmp(&self, other: &Box<'_, T>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
    #[inline]
    fn lt(&self, other: &Box<'_, T>) -> bool {
        PartialOrd::lt(&**self, &**other)
    }
    #[inline]
    fn le(&self, other: &Box<'_, T>) -> bool {
        PartialOrd::le(&**self, &**other)
    }
    #[inline]
    fn ge(&self, other: &Box<'_, T>) -> bool {
        PartialOrd::ge(&**self, &**other)
    }
    #[inline]
    fn gt(&self, other: &Box<'_, T>) -> bool {
        PartialOrd::gt(&**self, &**other)
    }
}

impl<T: ?Sized + Ord> Ord for Box<'_, T> {
    #[inline]
    fn cmp(&self, other: &Box<T>) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

impl<T: ?Sized + Eq> Eq for Box<'_, T> {}

impl<T: ?Sized + Hash> Hash for Box<'_, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<T: ?Sized + Hasher> Hasher for Box<'_, T> {
    fn finish(&self) -> u64 {
        (**self).finish()
    }
    fn write(&mut self, bytes: &[u8]) {
        (**self).write(bytes)
    }
    fn write_u8(&mut self, i: u8) {
        (**self).write_u8(i)
    }
    fn write_u16(&mut self, i: u16) {
        (**self).write_u16(i)
    }
    fn write_u32(&mut self, i: u32) {
        (**self).write_u32(i)
    }
    fn write_u64(&mut self, i: u64) {
        (**self).write_u64(i)
    }
    fn write_u128(&mut self, i: u128) {
        (**self).write_u128(i)
    }
    fn write_usize(&mut self, i: usize) {
        (**self).write_usize(i)
    }
    fn write_i8(&mut self, i: i8) {
        (**self).write_i8(i)
    }
    fn write_i16(&mut self, i: i16) {
        (**self).write_i16(i)
    }
    fn write_i32(&mut self, i: i32) {
        (**self).write_i32(i)
    }
    fn write_i64(&mut self, i: i64) {
        (**self).write_i64(i)
    }
    fn write_i128(&mut self, i: i128) {
        (**self).write_i128(i)
    }
    fn write_isize(&mut self, i: isize) {
        (**self).write_isize(i)
    }
}

impl<I: Iterator + ?Sized> Iterator for Box<'_, I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        (**self).next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (**self).size_hint()
    }
    fn nth(&mut self, n: usize) -> Option<I::Item> {
        (**self).nth(n)
    }
}

/// A memory arena, also known as a region-based allocator, or bump allocator.
///
/// See the the [module-level documentation](crate::arena) for more.
pub struct Arena<'src> {
    cursor: *mut MaybeUninit<u8>,
    end: *mut MaybeUninit<u8>,
    src: PhantomData<&'src mut ()>, // Ensures you can't allocate out of the source arena while this one is still alive
}

impl<'src> Arena<'src> {
    /// Constructs a new `Arena` allocating out of `buf`.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let arena = Arena::from_buffer(&mut backing_region[..]);
    /// ```
    #[inline]
    pub fn from_buffer(buf: &'src mut [MaybeUninit<u8>]) -> Arena<'src> {
        let Range { start, end } = buf.as_mut_ptr_range();

        Arena {
            cursor: start,
            end,
            src: PhantomData,
        }
    }

    /// Constructs a new `Arena` allocating out of the free space remaining in `self`.
    /// `self` cannot be used for allocation until the new arena is dropped.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from_buffer(&mut backing_region[..]);
    ///
    /// {
    ///     let mut tmp = arena.make_sub_arena();
    ///     let arr = tmp.alloc([0u32; 256]);      // this will take up all 1024 = 4*256 bytes...
    ///     assert!(tmp.try_alloc(0u8).is_none()); // ...so this can't succeed
    /// }
    ///
    /// assert!(arena.try_alloc([0u32; 256]).is_some()); // tmp was dropped, so the memory can be reused
    /// ```
    #[inline]
    pub fn make_sub_arena(&mut self) -> Arena<'_> {
        Arena {
            cursor: self.cursor,
            end: self.end,
            src: PhantomData,
        }
    }

    /// Constructs a new [`ArenaWriter`] backed by the free space remaining in `self`.
    /// Primarily intended for use in expansions of [`fmt!`](arena::fmt).
    #[inline]
    pub fn make_writer<'a>(&'a mut self) -> ArenaWriter<'a, 'src> {
        ArenaWriter {
            source: self,
            len: 0,
        }
    }

    #[inline]
    fn try_alloc_raw(&mut self, alloc_layout: &Layout) -> *mut MaybeUninit<u8> {
        let align_offset = self.cursor.align_offset(alloc_layout.align());

        // `ptr::align_offset()` returns `usize::MAX` when aligning the pointer
        // isn't possible, which shouldn't ever happen with a `*u8`, BUT:
        // the implementation is free to _always_ return `usize::MAX`, so
        // we'll leave getting rid of this check to the optimizer
        assert!(align_offset != usize::MAX);

        // we can't eagerly compute `result` and `new_cursor`, because it's UB
        // for the result of `ptr::add` to be out of bounds, so the correct way
        // to check bounds here is through usize arithmetic:
        if let Some(total_bytes) = align_offset.checked_add(alloc_layout.size()) {
            if (self.end as usize) - (self.cursor as usize) >= total_bytes {
                let result = unsafe { self.cursor.add(align_offset) };
                let new_cursor = unsafe { result.add(alloc_layout.size()) };
                self.cursor = new_cursor;

                return result;
            }
        }

        null_mut()
    }

    /// Allocates memory in the arena and then places the `Default` value for T
    /// into it.
    ///
    /// # Panics
    /// Panics if the remaining space in the arena is insufficient.
    /// See [`try_alloc_default`] for a checked version that never panics.
    #[inline]
    pub fn alloc_default<T: Default + Sized>(&mut self) -> Box<'src, T> {
        self.try_alloc(T::default()).unwrap()
    }

    /// Allocates memory in the arena and then places `x` into it.
    ///
    /// # Panics
    /// Panics if the remaining space in the arena is insufficient.
    /// See [`try_alloc`] for a checked version that never panics.
    #[inline]
    pub fn alloc<T: Sized>(&mut self, x: T) -> Box<'src, T> {
        self.try_alloc(x).unwrap()
    }

    /// Allocates memory in the arena and then places the `Default` value for T
    /// into it.
    ///
    /// Returns [`None`] if the remaining space in the arena is insufficient.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from_buffer(&mut backing_region[..]);
    ///
    /// for _ in 0..(1024 / 16) {
    ///     assert_eq!(*arena.try_alloc_default::<u128>().unwrap(), 0);
    /// }
    ///
    /// assert!(arena.try_alloc_default::<u128>().is_none());
    /// ```
    #[inline]
    pub fn try_alloc_default<T: Default + Sized>(&mut self) -> Option<Box<'src, T>> {
        self.try_alloc(T::default())
    }

    /// Allocates memory in the arena and then places `x` into it.
    ///
    /// Returns [`None`] if the remaining space in the arena is insufficient.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from_buffer(&mut backing_region[..]);
    ///
    /// for i in 0..(1024 / 16) {
    ///     assert_eq!(*arena.try_alloc(i as u128).unwrap(), i as u128);
    /// }
    ///
    /// assert!(arena.try_alloc(0xDEAD_BEEF_CAFE_BABEu128).is_none());
    /// ```
    #[inline]
    pub fn try_alloc<T: Sized>(&mut self, x: T) -> Option<Box<'src, T>> {
        let ptr = self.try_alloc_raw(&Layout::new::<T>());
        if ptr.is_null() {
            return None;
        }

        unsafe {
            let ptr = ptr as *mut T;
            ptr.write(x);

            Some(Box {
                ptr: NonNull::new_unchecked(ptr),
                val: PhantomData,
                src: PhantomData,
            })
        }
    }

    /// Allocates memory in the arena and then places `count` copies of the
    /// `Default` value for T into it.
    ///
    /// Consider using [`alloc_default<[T; count]>`](alloc_default) instead
    /// when `count` is known at compile time.
    ///
    /// # Panics
    /// Panics if the remaining space in the arena is insufficient.
    /// See [`try_array_default`] for a checked version that never panics.
    #[inline]
    pub fn array_default<T>(&mut self, count: usize) -> Box<'src, [T]>
    where
        T: Copy + Default + Sized,
    {
        self.try_array(T::default(), count).unwrap()
    }

    /// Allocates memory in the arena and then places `count` copies of `x`
    /// into it.
    ///
    /// Consider using [`alloc([x; count])`](alloc) instead when `count` is
    /// known at compile time.
    ///
    /// # Panics
    /// Panics if the remaining space in the arena is insufficient.
    /// See [`try_array`] for a checked version that never panics.
    #[inline]
    pub fn array<T>(&mut self, x: T, count: usize) -> Box<'src, [T]>
    where
        T: Copy + Sized,
    {
        self.try_array(x, count).unwrap()
    }

    /// Allocates memory in the arena and then places `count` copies of the
    /// `Default` value for T into it.
    ///
    /// Returns [`None`] if the remaining space in the arena is insufficient.
    ///
    /// Consider using [`try_alloc_default<[T; count]>`](try_alloc_default)
    /// instead when `count` is known at compile time.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from_buffer(&mut backing_region[..]);
    /// let array = arena.try_array_default::<u128>(16).unwrap();
    /// assert_eq!(&array[..], &[0; 16])
    /// ```
    #[inline]
    pub fn try_array_default<T>(&mut self, count: usize) -> Option<Box<'src, [T]>>
    where
        T: Copy + Default + Sized,
    {
        self.try_array(T::default(), count)
    }

    #[inline]
    fn try_array_raw<T>(&mut self, count: usize) -> *mut [MaybeUninit<T>]
    where
        T: Sized,
    {
        let empty = unsafe {
            // must not use null, even for empty slices, because of NonNull optimizations
            let mut dangling = NonNull::dangling();
            from_raw_parts_mut(dangling.as_mut(), 0) as *mut [MaybeUninit<T>]
        };

        let alloc_layout = match Layout::array::<T>(count) {
            Ok(layout) => layout,
            Err(_) => {
                return empty;
            }
        };

        let ptr = self.try_alloc_raw(&alloc_layout) as *mut T;
        if ptr.is_null() {
            return empty;
        }

        unsafe { from_raw_parts_mut(ptr, count) as *mut [T] as *mut [MaybeUninit<T>] }
    }

    /// Allocates memory in the arena and then places `count` copies of `x`
    /// into it.
    ///
    /// Returns [`None`] if the remaining space in the arena is insufficient.
    ///
    /// Consider using [`try_alloc([x; count])`](try_alloc) instead when
    /// `count` is known at compile time.
    ///
    /// # Examples
    /// ```
    /// use core::mem::MaybeUninit;
    /// use coca::Arena;
    ///
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from_buffer(&mut backing_region[..]);
    /// let array = arena.try_array(0x12345678u32, 256).unwrap();
    /// assert_eq!(&array[..], &[0x12345678u32; 256])
    /// ```
    #[inline]
    pub fn try_array<T>(&mut self, x: T, count: usize) -> Option<Box<'src, [T]>>
    where
        T: Copy + Sized,
    {
        let ptr = self.try_array_raw::<T>(count);
        if ptr.is_null() {
            return None;
        }

        unsafe {
            let ptr = ptr as *mut T;
            for i in 0..count {
                ptr.add(i).write(x);
            }

            let slice = from_raw_parts_mut(ptr, count);
            Some(Box {
                ptr: NonNull::new_unchecked(slice),
                val: PhantomData,
                src: PhantomData,
            })
        }
    }

    #[inline]
    pub fn list_with_capacity<T, I: AsIndex>(
        &mut self,
        capacity: usize,
    ) -> BoxSliceList<'src, T, I> {
        self.try_list_with_capacity(capacity).unwrap()
    }

    #[inline]
    pub fn try_list_with_capacity<T, I: AsIndex>(
        &mut self,
        capacity: usize,
    ) -> Option<BoxSliceList<'src, T, I>> {
        let ptr = self.try_array_raw::<T>(capacity);
        if ptr.is_null() {
            return None;
        }
        let buf = Box {
            ptr: unsafe { NonNull::new_unchecked(ptr) },
            val: PhantomData,
            src: PhantomData,
        };

        Some(List::from_buffer(buf))
    }

    #[cfg(feature = "nightly")]
    #[inline]
    pub fn array_list<T, I: AsIndex, const N: usize>(&mut self) -> BoxArrayList<'src, T, I, N> {
        self.try_array_list().unwrap()
    }

    #[cfg(feature = "nightly")]
    #[inline]
    pub fn try_array_list<T, I: AsIndex, const N: usize>(
        &mut self,
    ) -> Option<BoxArrayList<'src, T, I, N>> {
        let alloc_layout = Layout::new::<[T; N]>();
        let ptr = self.try_alloc_raw(&alloc_layout) as *mut [T; N];
        if ptr.is_null() {
            return None;
        }

        let buf = Box {
            ptr: unsafe { NonNull::new_unchecked(ptr as *mut [MaybeUninit<T>; N]) },
            val: PhantomData,
            src: PhantomData,
        };

        Some(List::from_buffer(buf))
    }

    #[inline]
    pub fn collect<T, I>(&mut self, iter: I) -> Box<'src, [T]>
    where
        T: Sized,
        I: IntoIterator<Item = T>,
    {
        self.try_collect(iter).unwrap()
    }

    pub fn try_collect<T, I>(&mut self, iter: I) -> Option<Box<'src, [T]>>
    where
        T: Sized,
        I: IntoIterator<Item = T>,
    {
        let alloc_layout = Layout::new::<T>();
        let align_offset = self.cursor.align_offset(alloc_layout.align());
        assert!(align_offset != usize::MAX);

        let bytes_remaining = (self.end as usize) - (self.cursor as usize);
        if bytes_remaining < align_offset {
            return None;
        }

        let item_capacity = (bytes_remaining - align_offset) / core::mem::size_of::<T>();

        let base = unsafe { self.cursor.add(align_offset) as *mut T };
        let mut count = 0usize;
        let mut cursor = base;

        for val in iter {
            if count == item_capacity {
                for i in 0..count {
                    unsafe {
                        base.add(i).drop_in_place();
                    }
                }

                return None;
            }

            count += 1;
            unsafe {
                cursor.write(val);
                cursor = cursor.add(1);
            }
        }

        self.cursor = cursor as *mut MaybeUninit<u8>;

        unsafe {
            let slice = from_raw_parts_mut(base, count);
            Some(Box {
                ptr: NonNull::new_unchecked(slice),
                val: PhantomData,
                src: PhantomData,
            })
        }
    }
}

/// Implementor of [`core::fmt::Write`] backed by an [`Arena`].
/// Primarily intended for use in expansions of [`fmt!`](arena::fmt).
///
/// # Examples
/// ```
/// use coca::{Arena, Box};
/// use core::{fmt::Write, mem::MaybeUninit};
///
/// let mut backing_buffer = [MaybeUninit::uninit(); 1024];
/// let mut arena = Arena::from_buffer(&mut backing_buffer[..]);
/// let str = {
///     let mut writer = arena.make_writer();
///     core::write!(writer, "Testing, testing, {}, {}, {}...", 1, 2, 3).unwrap();
///     Box::<'_, str>::from(writer)
/// };
/// assert_eq!(&str[..], "Testing, testing, 1, 2, 3...");
/// ```
pub struct ArenaWriter<'src, 'buf> {
    source: &'src mut Arena<'buf>,
    len: usize,
}

impl Write for ArenaWriter<'_, '_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let bytes_remaining = (self.source.end as usize) - (self.source.cursor as usize);
        if s.len() > bytes_remaining {
            return fmt::Result::Err(fmt::Error);
        }

        unsafe {
            s.as_ptr()
                .copy_to_nonoverlapping(self.source.cursor as *mut u8, s.len());
        }

        self.source.cursor = unsafe { self.source.cursor.add(s.len()) };
        self.len += s.len();

        Ok(())
    }
}

impl<'buf> From<ArenaWriter<'_, 'buf>> for Box<'buf, str> {
    fn from(writer: ArenaWriter<'_, 'buf>) -> Self {
        unsafe {
            let ptr = writer.source.cursor.sub(writer.len) as *mut u8;
            let slice = from_raw_parts_mut(ptr, writer.len);
            let str_ptr = NonNull::new_unchecked(slice).as_ptr() as *mut str;

            Box {
                ptr: NonNull::new_unchecked(str_ptr),
                val: PhantomData,
                src: PhantomData,
            }
        }
    }
}

/// Creates a `Option<Box<'_, str>>` using interpolation of runtime expressions.
///
/// The first argument `fmt!` receives is an [`Arena`] from which the string
/// will be allocated.
///
/// The second argument is a format string. This must be a string literal.
/// Additional parameters passed to `fmt!` replace the `{}`s contained within
/// the formatting string in the order given unless named or positional
/// parameters are used; see [`core::fmt`] for more information.
///
/// Evaluates to `None` if the arena does not have enough space remaining to
/// contain the formatted string.
///
/// # Examples
/// ```
/// use coca::{Arena, fmt};
/// use core::mem::MaybeUninit;
///
/// let mut backing_buffer = [MaybeUninit::uninit(); 16];
/// let mut arena = Arena::from_buffer(&mut backing_buffer[..]);
/// let output = fmt!(arena, "test").unwrap();
/// let output = fmt!(arena, "hello {}", "world!").unwrap();
/// assert!(fmt!(arena, "{}", ' ').is_none());
/// ```
#[macro_export]
macro_rules! fmt {
    ($arena:expr, $($arg:tt)*) => {{
        use core::fmt::Write;
        let mut writer = $arena.make_writer();
        core::write!(writer, $($arg)*)
            .ok()
            .map(|_| $crate::Box::<'_, str>::from(writer))
    }}
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::size_of;

    #[test]
    fn it_works() {
        let mut backing_store = [MaybeUninit::uninit(); 256];
        let mut arena = Arena::from_buffer(&mut backing_store[..]);

        enum BinTree<'a> {
            Leaf(i32),
            Branch(Box<'a, BinTree<'a>>, Box<'a, BinTree<'a>>),
        }

        let a = arena.alloc(BinTree::Leaf(0));
        let b = arena.alloc(BinTree::Leaf(1));
        let mut c = arena.alloc(BinTree::Branch(a, b));

        {
            let mut sub_arena = arena.make_sub_arena();

            match c.as_mut() {
                BinTree::Branch(left, _) => {
                    // NOTE: This is legal _only_ because we move c into _e later on!
                    *left = sub_arena.alloc(BinTree::Leaf(2));
                }
                BinTree::Leaf(_) => {}
            }

            let d = sub_arena.alloc(BinTree::Leaf(0));
            let _e = sub_arena.alloc(BinTree::Branch(c, d));
        };

        let mut arr = arena.array_default::<i32>(4);
        assert_eq!(arr.as_ref(), &[0, 0, 0, 0]);

        arr[0] = 0;
        arr[1] = 1;
        arr[2] = 4;
        arr[3] = 9;

        assert_eq!(size_of::<Option<Box<'_, BinTree>>>(), size_of::<usize>());
        assert_eq!(size_of::<Box<'_, [i32]>>(), 2 * size_of::<usize>());
        assert_eq!(arr.len(), 4);
    }

    #[test]
    fn collect_iter() {
        let mut backing_memory = [MaybeUninit::uninit(); 256];
        let mut arena = Arena::from_buffer(&mut backing_memory[..]);
        let nums = arena.collect(0..60i32);

        assert_eq!(nums.len(), 60);
        assert_eq!(&nums[0..8], &[0, 1, 2, 3, 4, 5, 6, 7]);
        assert_eq!(&nums[52..], &[52, 53, 54, 55, 56, 57, 58, 59]);

        // Assert that all values taken from the iterator are correctly dropped
        // if there's not enough space available to exhaust it.
        //
        // At this point, there should be 16 free bytes left in the arena,
        // enough to store 2 or 4 references (depending on the size of a
        // pointer). One additional value will be pulled from the iterator
        // (though it won't be written into the arena), at which point it and
        // all previously written values should be dropped.

        use core::cell::Cell;
        struct Droppable<'a> {
            drop_count: &'a Cell<usize>,
        }

        impl Drop for Droppable<'_> {
            fn drop(&mut self) {
                let count = self.drop_count.get();
                self.drop_count.set(count + 1);
            }
        }

        let drop_count = Cell::new(0);

        let result = arena.try_collect((0..8).map(|_| Droppable {
            drop_count: &drop_count,
        }));

        assert!(result.is_none());
        assert_eq!(drop_count.get(), 1 + 16 / core::mem::size_of::<Droppable>());
    }

    #[test]
    fn format_strings() {
        let mut backing_memory = [MaybeUninit::uninit(); 256];
        let mut arena = Arena::from_buffer(&mut backing_memory[..]);

        #[derive(Debug)]
        struct LinkedList<'a> {
            val: i64,
            next: Option<Box<'a, LinkedList<'a>>>,
        }

        let a = arena.alloc(LinkedList { val: 0, next: None });
        let b = arena.alloc(LinkedList {
            val: 1,
            next: Some(a),
        });

        let output = fmt!(arena, "{:?}", b).unwrap();

        let _c = arena.alloc(LinkedList {
            val: 2,
            next: Some(b),
        });

        assert_eq!(
            output.as_ref(),
            "LinkedList { val: 1, next: Some(LinkedList { val: 0, next: None }) }"
        );
    }

    #[test]
    fn lists() {
        let mut backing_memory = [MaybeUninit::uninit(); 256];
        let mut arena = Arena::from_buffer(&mut backing_memory[..]);

        let mut list_a = arena.list_with_capacity::<i32, usize>(32);
        let mut list_b = arena.list_with_capacity::<i32, usize>(32);
        assert!(arena.try_alloc(0u8).is_none());

        for i in 1..=32 {
            list_a.push(i);
        }

        for i in &list_a {
            list_b.push(-i);
        }

        assert_eq!(&list_b.as_slice()[..8], &[-1, -2, -3, -4, -5, -6, -7, -8]);
    }
}
