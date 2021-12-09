//! UTF-8 encoded, growable string types with constant capacity.

use core::fmt::{self, Display};
use core::str::{self, Utf8Error};

use crate::storage::{ArrayLike, Storage, Capacity, InlineStorage, ArenaStorage};
use crate::vec::Vec;

/// A possible error value when converting a UTF-8 byte vector into a [`String`].
/// 
/// This is the error type for the [`from_utf8`] method on `String`.
/// 
/// [`from_utf8`]: String::from_utf8
#[derive(Debug, PartialEq, Eq)]
pub struct FromUtf8Error<S: Storage<ArrayLike<u8>>, I: Capacity> {
    bytes: Vec<u8, S, I>,
    error: Utf8Error,
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> FromUtf8Error<S, I> {
    /// Returns a slice of bytes that were attempted to convert to a [`String`].
    pub fn as_bytes(&self) -> &[u8] {
        self.bytes.as_slice()
    }

    /// Returns the byte vector that was attempted to convert to a [`String`].
    pub fn into_bytes(self) -> Vec<u8, S, I> {
        self.bytes
    }

    /// Returns a [`Utf8Error`] that provides more details about the conversion failure.
    pub fn utf8_error(&self) -> Utf8Error {
        self.error
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> Clone for FromUtf8Error<S, I> where Vec<u8, S, I>: Clone {
    fn clone(&self) -> Self {
        FromUtf8Error {
            bytes: self.bytes.clone(),
            error: self.error,
        }
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> Display for FromUtf8Error<S, I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

/// A UTF-8 encoded, growable string.
/// 
/// Generic over the storage buffer type `S` and the index type `I`.
pub struct String<S: Storage<ArrayLike<u8>>, I: Capacity = usize> {
    vec: Vec<u8, S, I>,
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> From<S> for String<S, I> {
    fn from(buf: S) -> Self {
        String { vec: Vec::from(buf) }
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> String<S, I> {
    /// Converts a vector of bytes into a `String` without copying.
    /// 
    /// If you are sure that the byte vector is valid UTF-8, and don't want to
    /// incur the overhead of the validity check, consider [`from_utf8_unchecked`],
    /// which has the same behavior but skips the check.
    /// 
    /// If you need a [`&str`] instead of a `String`, consider [`str::from_utf8`].
    /// 
    /// The inverse of this method is [`into_bytes`].
    /// 
    /// [`from_utf8_unchecked`]: String::from_utf8_unchecked
    /// [`&str`]: prim@str "&str"
    /// [`into_bytes`]: String::into_bytes
    /// 
    /// # Errors
    /// Returns [`Err`] if the slice is not UTF-8 with a description as to why
    /// the provided bytes are not UTF-8. The moved vector is also included.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    #[inline]
    pub fn from_utf8(vec: Vec<u8, S, I>) -> Result<Self, FromUtf8Error<S, I>> {
        match core::str::from_utf8(&vec) {
            Ok(_) => Ok(String { vec }),
            Err(e) => Err(FromUtf8Error { bytes: vec, error: e }),
        }
    }

    // TODO: from_utf8_lossy, from_utf16

    /// Decomposes a `String` into its raw parts.
    /// 
    /// Returns the raw storage type and the length of the string (in bytes).
    /// These are the same arguments in the same order as the arguments to
    /// [`from_raw_parts`](String::from_raw_parts).
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    #[inline]
    pub fn into_raw_parts(self) -> (S, I) {
        self.vec.into_raw_parts()
    }

    /// Creates a new `String` from a length and raw storage buffer.
    /// 
    /// # Safety
    /// Callers must ensure that
    /// 
    /// * `length` is less than or equal to `buf.capacity()`, and
    /// * the first `length` bytes stored in `buf` are valid UTF-8.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    #[inline]
    pub unsafe fn from_raw_parts(buf: S, length: I) -> Self {
        String { vec: Vec::from_raw_parts(buf, length) }
    }

    /// Converts a vector of bytes into a `String` without copying or checking
    /// that the bytes are valid UTF-8.
    /// 
    /// See the safe version, [`from_utf8`], for more details.
    /// 
    /// [`from_utf8`]: String::from_utf8
    /// 
    /// # Safety
    /// 
    /// Callers must ensure that the passed bytes are valid UTF-8. If this
    /// constraint is violated, it may cause memory unsafety issues with future
    /// users of the `String`, as the rest of `coca` assumes `String`s to be
    /// valid UTF-8.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    #[inline]
    pub unsafe fn from_utf8_unchecked(bytes: Vec<u8, S, I>) -> Self {
        String { vec: bytes }
    }

    /// Converts a `String` into a vector of bytes without copying, consuming the string.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    #[inline]
    pub fn into_bytes(self) -> Vec<u8, S, I> {
        self.vec
    }

    /// Extracts a string slice containing the entire `String`.
    pub fn as_str(&self) -> &str {
        self
    }

    /// Extracts a mutable string slice containing the entire `String`.
    pub fn as_mut_str(&mut self) -> &mut str {
        self
    }

    /// Appends a given string slice onto the end of the `String`, returning
    /// [`Err`] if the remaining space is insufficient.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    #[inline]
    pub fn try_push_str(&mut self, string: &str) -> Result<(), ()> {
        self.vec.try_extend_from_slice(string.as_bytes())
    }

    /// Appends a given string slice onto the end of the `String`.
    /// 
    /// # Panics
    /// Panics if the space remaining in the string is insufficient.
    /// See [`try_push_str`](String::try_push_str) for a checked version
    /// that never panics.
    #[inline]
    pub fn push_str(&mut self, string: &str) {
        #[cold]
        #[inline(never)]
        fn assert_failed() -> ! {
            panic!("space remaining in string is insufficient")
        }

        if self.try_push_str(string).is_err() {
            assert_failed();
        }
    }

    // TODO: extend_from_within

    /// Returns the `String`'s capacity, in bytes.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.vec.capacity()
    }

    /// Returns the current length of the `String`, in bytes, not [`char`]s or
    /// graphemes. This might not be what a human considers the length of the string.
    #[inline]
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// Returns `true` if the `String` has a length of zero, and `false` otherwise.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if the `String` has a length equal to its capacity, and `false` otherwise.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len() == self.capacity()
    }

    /// Appends the given [`char`] to the end of the `String`, returning
    /// `Err(ch)` if the remaining space is insufficient.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    #[inline]
    pub fn try_push(&mut self, ch: char) -> Result<(), ()> {
        match ch.len_utf8() {
            1 => self.vec.try_push(ch as u8).map_err(|_| ()),
            _ => self.vec.try_extend_from_slice(ch.encode_utf8(&mut [0; 4]).as_bytes())
        }
    }

    /// Appends the given [`char`] to the end of the `String`.
    /// 
    /// # Panics
    /// Panics if the space remaining in the string is insufficient.
    /// See [`try_push`](String::try_push_str) for a checked version
    /// that never panics.
    #[inline]
    pub fn push(&mut self, ch: char) {
        #[cold]
        #[inline(never)]
        fn assert_failed() -> ! {
            panic!("space remaining in string is insufficient")
        }

        if self.try_push(ch).is_err() {
            assert_failed();
        }
    }

    /// Returns a byte slice of this `String`'s contents.
    /// 
    /// The inverse of this method is [`from_utf8`](String::from_utf8).
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.vec
    }

    /// Shortens the `String` to the specified length.
    /// 
    /// If `new_len` is greater than the string's current length, this has no effect.
    /// 
    /// # Panics
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            self.vec.truncate(I::from_usize(new_len));
        }
    }

    /// Truncates the `String`, removing all contents.
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Removes the last [`char`] from the `String` and returns it,
    /// or [`None`] if it is empty.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().rev().next()?;
        let newlen = I::from_usize(self.len() - ch.len_utf8());
        unsafe { self.vec.set_len(newlen); }
        Some(ch)
    }

    /// Removes a [`char`] at the given byte position from the `String` and returns it.
    /// 
    /// This is an *O*(*n*) operation, as it requires copying every character
    /// after the removed element in the string.
    /// 
    /// # Panics
    /// Panics if `idx` is larger than or equal to the string's length,
    /// or if it does not lie on a [`char`] boundary.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    pub fn remove(&mut self, idx: usize) -> char {
        let result = self[idx..].chars().next().expect("cannot remove a char from the end of a string");
        
        let next = idx + result.len_utf8();
        let len = self.len();
        let new_len = I::from_usize(len - (next - idx));

        unsafe {
            core::ptr::copy(self.vec.as_ptr().add(next), self.vec.as_mut_ptr().add(idx), len - next);
            self.vec.set_len(new_len);
        }

        result
    }

    // TODO:
    // pub fn retain<F: FnMut(char) -> bool>(&mut self, mut f: F) {}
    // pub fn insert(&mut self, idx: usize, ch: char) {}
    // pub fn insert_str(&mut self, idx: usize, string: &str) {}
    
    /// Returns a mutable reference to the raw byte contents of this `String`.
    /// 
    /// # Safety
    /// This function is unsafe because the returned `&mut Vec` allows writing
    /// bytes which are not valid UTF-8. If this constraint is violated, using
    /// the original `String` after dropping the `&mut Vec` may violate memory
    /// safety, as the rest of `coca` assumes that `String`s are valid UTF-8.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    #[inline]
    pub unsafe fn as_mut_vec(&mut self) -> &mut Vec<u8, S, I> {
        &mut self.vec
    }
    
    // TODO:
    // pub fn split_off(&mut self, at: usize) -> String<???> {} // define this only for some storage types?
    // pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> Drain<'_> {}
    // pub fn replace_range<R: RangeBounds<usize>>(&mut self, range: R, replace_with: &str) {}
    // pub fn into_boxed_str(self) -> Box<str> // define this only for some storage types...
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> core::ops::Deref for String<S, I> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        unsafe { str::from_utf8_unchecked(&self.vec) }
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> core::ops::DerefMut for String<S, I> {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(&mut *self.vec) }
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> core::convert::AsRef<str> for String<S, I> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> core::convert::AsMut<str> for String<S, I> {
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> core::convert::AsRef<[u8]> for String<S, I> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.vec.as_slice()
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> Clone for String<S, I> where Vec<u8, S, I>: Clone {
    #[inline]
    fn clone(&self) -> Self {
        String { vec: self.vec.clone() }
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> core::iter::Extend<char> for String<S, I> {
    #[inline]
    fn extend<It: IntoIterator<Item = char>>(&mut self, iter: It) {
        for ch in iter {
            self.push(ch);
        }
    }
}

impl<'a, S: Storage<ArrayLike<u8>>, I: Capacity> core::iter::Extend<&'a char> for String<S, I> {
    #[inline]
    fn extend<It: IntoIterator<Item = &'a char>>(&mut self, iter: It) {
        for ch in iter {
            self.push(*ch);
        }
    }
}

impl<'a, S: Storage<ArrayLike<u8>>, I: Capacity> core::iter::Extend<&'a str> for String<S, I> {
    #[inline]
    fn extend<It: IntoIterator<Item = &'a str>>(&mut self, iter: It) {
        for s in iter {
            self.push_str(s);
        }
    }
}

impl<S1: Storage<ArrayLike<u8>>, I1: Capacity, S2: Storage<ArrayLike<u8>>, I2: Capacity> PartialEq<String<S2, I2>> for String<S1, I1> {
    #[inline]
    fn eq(&self, other: &String<S2, I2>) -> bool {
        self.as_str() == other.as_str()
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> Eq for String<S, I> {}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> PartialEq<str> for String<S, I> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> PartialEq<&str> for String<S, I> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl<S1: Storage<ArrayLike<u8>>, I1: Capacity, S2: Storage<ArrayLike<u8>>, I2: Capacity> PartialOrd<String<S2, I2>> for String<S1, I1> {
    #[inline]
    fn partial_cmp(&self, other: &String<S2, I2>) -> Option<core::cmp::Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> Ord for String<S, I> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> fmt::Display for String<S, I> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> fmt::Debug for String<S, I> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> fmt::Write for String<S, I> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.try_push_str(s).map_err(|_| fmt::Error)
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
        self.try_push(c).map_err(|_| fmt::Error)
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> core::hash::Hash for String<S, I> {
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, hasher: &mut H) {
        (**self).hash(hasher)
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> core::ops::Add<&str> for String<S, I> {
    type Output = Self;

    #[inline]
    fn add(mut self, other: &str) -> Self {
        self.push_str(other);
        self
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> core::ops::AddAssign<&str> for String<S, I> {
    #[inline]
    fn add_assign(&mut self, rhs: &str) {
        self.push_str(rhs);
    }
}

/// A string using an arena-allocated byte slice for storage.
/// 
/// # Examples
/// ```
/// todo!()
/// ```
pub type ArenaString<'a, I = usize> = String<ArenaStorage<'a, ArrayLike<u8>>, I>;

impl<'a, I: Capacity> ArenaString<'a, I> {
    /// Converts the given boxed `str` slice into a `String`.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    pub fn from_boxed_str(mut string: crate::arena::Box<'a, str>) -> Self {
        let length = string.len();
        unsafe { 
            let buf = ArenaStorage::from_raw_parts(string.as_mut_ptr(), length).unwrap();
            Self::from_raw_parts(buf, I::from_usize(length))
        }
    }

    /// Converts the `ArenaString` into an owned `str` slice.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    pub fn into_boxed_str(self) -> crate::arena::Box<'a, str> {
        let (mut buf, len) = self.into_raw_parts();
        let ptr = core::ptr::slice_from_raw_parts_mut(buf.get_mut_ptr(), len.as_usize());
        unsafe {
            let str_ptr = core::str::from_utf8_unchecked_mut(ptr.as_mut().unwrap());
            crate::arena::Box::new_unchecked(str_ptr as *mut str)
        }
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
/// A string using a heap-allocated slice for storage.
/// 
/// # Examples
/// ```
/// todo!()
/// ```
pub type AllocString<I = usize> = String<crate::storage::AllocStorage<ArrayLike<u8>>, I>;

#[cfg(feature = "alloc")]
#[cfg_attr(docs_rs, doc(cfg(feature = "alloc")))]
impl<I: Capacity> String<crate::storage::AllocStorage<ArrayLike<u8>>, I> {
    /// Creates a new, empty `AllocString` with the specified capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::from(crate::storage::AllocStorage::with_capacity(capacity))
    }

    /// Creates a new `AllocString` with the given contents, and zero excess capacity.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    pub fn from_str(string: &str) -> Self {
        let mut buf = Self::with_capacity(string.len());
        buf.push_str(string);
        buf
    }

    /// Creates a new `AllocString` with the given capacity, and initializes it with the given content.
    /// 
    /// Returns [`Err`] if the given string is longer (in bytes) than `capacity`.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    pub fn try_from_str_with_capacity(string: &str, capacity: usize) -> Result<Self, ()> {
        if string.len() > capacity { return Err(()); }

        let mut buf = Self::with_capacity(capacity);
        buf.push_str(string);
        Ok(buf)
    }

    /// Creates a new `AllocString` with the given capacity, and initializes it with the given content.
    /// 
    /// # Panics
    /// Panics if the given string is longer (in bytes) than `capacity`.
    /// See [`try_from_str_with_capacity`](String::try_from_str_with_capacity)
    /// for a checked version that never panics.
    pub fn from_str_with_capacity(string: &str, capacity: usize) -> Self {
        Self::try_from_str_with_capacity(string, capacity).expect("given string is longer than capacity")
    }
}

/// A string using an inline array for storage.
/// 
/// # Examples
/// ```
/// todo!()
/// ```
pub type InlineString<const C: usize> = String<InlineStorage<u8, C>, usize>;
/// A string using an inline array for storage, generic over the index type.
/// 
/// # Examples
/// ```
/// todo!()
/// ```
pub type TiInlineString<I, const C: usize> = String<InlineStorage<u8, C>, I>;

impl<I: Capacity, const C: usize> String<InlineStorage<u8, C>, I> {
    /// Constructs a new, empty `String` backed by an inline array.
    pub fn new() -> Self {
        String { vec: Vec::new() }
    }

    /// Constructs a new `String` backed by an inline array, initialized with the given contents.
    /// 
    /// Returns [`Err`] if the given string is longer than `C` bytes.
    /// 
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    pub fn try_from_str(string: &str) -> Result<Self, ()> {
        if string.len() <= C {
            let mut result = Self::new();
            result.push_str(string);
            Ok(result)
        } else {
            Err(())
        }
    }

    /// Constructs a new `String` backed by an inline array, initialized with the given contents.
    /// 
    /// # Panics
    /// Panics if the given string is longer than `C` bytes.
    /// See [`try_from_str`](String::try_from_str) for a checked version that never panics.
    pub fn from_str(string: &str) -> Self {
        Self::try_from_str(string).expect("given string is longer than capacity")
    }
}

impl<I: Capacity, const C: usize> Default for String<InlineStorage<u8, C>, I> {
    fn default() -> Self {
        Self::new()
    }
}

