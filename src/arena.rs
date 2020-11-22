use core::alloc::Layout;
use core::cmp::Ordering;
use core::fmt::{self, Debug, Display, Formatter, Pointer, Write};
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut, Range};
use core::ptr::{null_mut, NonNull};
use core::slice::from_raw_parts_mut;

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
    #[inline]
    fn ne(&self, other: &Box<'_, T>) -> bool {
        PartialEq::ne(&**self, &**other)
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

pub struct Arena<'src> {
    cursor: *mut MaybeUninit<u8>,
    end: *mut MaybeUninit<u8>,
    src: PhantomData<&'src mut ()>, // Ensures you can't allocate out of the source arena while this one is still alive
}

impl<'src> Arena<'src> {
    pub fn from_buffer(buf: &'src mut [MaybeUninit<u8>]) -> Arena<'src> {
        let Range { start, end } = buf.as_mut_ptr_range();

        Arena {
            cursor: start,
            end,
            src: PhantomData,
        }
    }

    pub fn make_sub_arena<'a>(&'a mut self) -> Arena<'a> {
        Arena {
            cursor: self.cursor,
            end: self.end,
            src: PhantomData,
        }
    }

    pub fn make_writer<'a>(&'a mut self) -> ArenaWriter<'a, 'src> {
        ArenaWriter {
            source: self,
            len: 0,
        }
    }

    fn try_alloc_raw(&mut self, alloc_layout: &Layout) -> *mut MaybeUninit<u8> {
        let align_offset = self.cursor.align_offset(alloc_layout.align());
        assert!(align_offset != usize::MAX);

        let result = unsafe { self.cursor.offset(align_offset as isize) };
        let new_cursor = unsafe { result.offset(alloc_layout.size() as isize) };
        if new_cursor <= self.end {
            self.cursor = new_cursor;
            result
        } else {
            null_mut()
        }
    }

    pub fn alloc_default<T: Default + Sized>(&mut self) -> Box<'src, T> {
        self.try_alloc(T::default()).unwrap()
    }

    pub fn alloc<T: Sized>(&mut self, val: T) -> Box<'src, T> {
        self.try_alloc(val).unwrap()
    }

    pub fn try_alloc_default<T: Default + Sized>(&mut self) -> Option<Box<'src, T>> {
        self.try_alloc(T::default())
    }

    pub fn try_alloc<T: Sized>(&mut self, val: T) -> Option<Box<'src, T>> {
        let ptr = self.try_alloc_raw(&Layout::new::<T>());
        if ptr.is_null() {
            return None;
        }

        unsafe {
            let ptr = ptr as *mut T;
            ptr.write(val);

            Some(Box {
                ptr: NonNull::new_unchecked(ptr),
                val: PhantomData,
                src: PhantomData,
            })
        }
    }

    pub fn array_default<T>(&mut self, count: usize) -> Box<'src, [T]>
    where
        T: Copy + Default + Sized,
    {
        self.try_array(T::default(), count).unwrap()
    }

    pub fn array<T>(&mut self, val: T, count: usize) -> Box<'src, [T]>
    where
        T: Copy + Sized,
    {
        self.try_array(val, count).unwrap()
    }

    pub fn try_array_default<T>(&mut self, count: usize) -> Option<Box<'src, [T]>>
    where
        T: Copy + Default + Sized,
    {
        self.try_array(T::default(), count)
    }

    pub fn try_array<T>(&mut self, val: T, count: usize) -> Option<Box<'src, [T]>>
    where
        T: Copy + Sized,
    {
        let alloc_layout = Layout::array::<T>(count).ok()?;

        let ptr = self.try_alloc_raw(&alloc_layout);
        if ptr.is_null() {
            return None;
        }

        unsafe {
            let ptr = ptr as *mut T;
            for i in 0..count {
                ptr.offset(i as isize).write(val);
            }

            let slice = from_raw_parts_mut(ptr, count);
            Some(Box {
                ptr: NonNull::new_unchecked(slice),
                val: PhantomData,
                src: PhantomData,
            })
        }
    }

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

        let base = unsafe { self.cursor.offset(align_offset as isize) as *mut T };
        let mut count = 0usize;
        let mut cursor = base;

        for val in iter {
            let next_cursor = unsafe { cursor.offset(1) };
            if (next_cursor as *mut MaybeUninit<u8>) > self.end {
                for i in 0..count {
                    unsafe {
                        base.offset(i as isize).drop_in_place();
                    }
                }

                return None;
            }

            unsafe {
                cursor.write(val);
            }

            count += 1;
            cursor = next_cursor;
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

pub struct ArenaWriter<'src, 'buf> {
    source: &'src mut Arena<'buf>,
    len: usize,
}

impl Write for ArenaWriter<'_, '_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let new_cursor = unsafe { self.source.cursor.offset(s.len() as isize) };

        if new_cursor > self.source.end {
            return fmt::Result::Err(fmt::Error);
        }

        unsafe {
            s.as_ptr()
                .copy_to_nonoverlapping(self.source.cursor as *mut u8, s.len());
        }

        self.source.cursor = new_cursor;
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

#[macro_export]
macro_rules! fmt {
    ($arena:expr, $($arg:tt)*) => {{
        let mut writer = $arena.make_writer();
        core::write!(writer, $($arg)*)
            .ok()
            .map(|_| Box::<'_, str>::from(writer))
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
}
