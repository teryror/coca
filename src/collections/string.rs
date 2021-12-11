//! UTF-8 encoded, growable string types with constant capacity.

use core::fmt::{self, Display};
use core::ops::{RangeBounds, Range};
use core::str::{self, Utf8Error};

use crate::collections::vec::Vec;
use crate::storage::{ArrayLike, Storage, Capacity, InlineStorage, ArenaStorage, normalize_range};

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
    /// // Basic Usage:
    /// let mut bytes = coca::collections::InlineVec::<u8, 8>::new();
    /// bytes.extend_from_slice(&[240, 159, 146, 150]);
    /// 
    /// let sparkle_heart = coca::collections::InlineString::from_utf8(bytes).unwrap();
    /// assert_eq!(sparkle_heart, "💖");
    /// 
    /// // Invalid Bytes:
    /// let mut bytes = coca::collections::InlineVec::<u8, 8>::new();
    /// bytes.extend_from_slice(&[0, 159, 146, 150]);
    /// assert!(coca::collections::InlineString::from_utf8(bytes).is_err());
    /// ```
    #[inline]
    pub fn from_utf8(vec: Vec<u8, S, I>) -> Result<Self, FromUtf8Error<S, I>> {
        match core::str::from_utf8(&vec) {
            Ok(_) => Ok(String { vec }),
            Err(e) => Err(FromUtf8Error { bytes: vec, error: e }),
        }
    }

    /// Decomposes a `String` into its raw parts.
    /// 
    /// Returns the raw storage type and the length of the string (in bytes).
    /// These are the same arguments in the same order as the arguments to
    /// [`from_raw_parts`](String::from_raw_parts).
    /// 
    /// # Examples
    /// ```
    /// let s = coca::collections::InlineString::<8>::from_str("hello");
    /// let (storage, len): ([core::mem::MaybeUninit<u8>; 8], usize) = s.into_raw_parts();
    /// assert_eq!(len, 5);
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
    /// use coca::collections::InlineString;
    /// 
    /// let s = InlineString::<8>::from_str("hello");
    /// let (storage, len) = s.into_raw_parts();
    /// 
    /// let rebuilt = unsafe { InlineString::from_raw_parts(storage, len) };
    /// assert_eq!(rebuilt, "hello");
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
    /// let mut bytes = coca::collections::InlineVec::<u8, 8>::new();
    /// bytes.extend_from_slice(&[240, 159, 146, 150]);
    /// 
    /// let sparkle_heart = unsafe { coca::collections::InlineString::from_utf8_unchecked(bytes) };
    /// assert_eq!(sparkle_heart, "💖");
    /// ```
    #[inline]
    pub unsafe fn from_utf8_unchecked(bytes: Vec<u8, S, I>) -> Self {
        String { vec: bytes }
    }

    /// Converts a `String` into a vector of bytes without copying, consuming the string.
    /// 
    /// # Examples
    /// ```
    /// let s = coca::collections::InlineString::<8>::from_str("hello");
    /// let bytes = s.into_bytes();
    /// 
    /// assert_eq!(&[104, 101, 108, 108, 111][..], &bytes[..]);
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
    /// let mut s = coca::collections::InlineString::<8>::from_str("foo");
    /// 
    /// assert!(s.try_push_str("bar").is_ok());
    /// 
    /// assert!(s.try_push_str("bazz").is_err());
    /// assert_eq!(s, "foobar");
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

    /// Copies characters from the `src` range to the end of the string.
    /// 
    /// Returns [`Err`] if the remaining space is insufficient.
    /// 
    /// # Panics
    /// Panics if the starting point is greater than the end point, if the end
    /// point is greater than the length of the `String`, or if either one does
    /// not lie on a [`char`] boundary.
    /// 
    /// # Examples
    /// ```
    /// let mut s = coca::collections::InlineString::<10>::from_str("abcde");
    /// 
    /// assert!(s.try_extend_from_within(2..).is_ok());
    /// assert_eq!(s, "abcdecde");
    /// 
    /// assert!(s.try_extend_from_within(..2).is_ok());
    /// assert_eq!(s, "abcdecdeab");
    /// 
    /// assert!(s.try_extend_from_within(4..8).is_err());
    /// ```
    pub fn try_extend_from_within<R: RangeBounds<usize>>(&mut self, src: R) -> Result<(), ()> {
        let Range { start, end } = normalize_range(src, self.len());

        assert!(self.is_char_boundary(start));
        assert!(self.is_char_boundary(end));

        let src = I::from_usize(start)..I::from_usize(end);
        self.vec.try_extend_from_within(src)
    }

    /// Copies the characters from the `src` range to the end of the string.
    /// 
    /// # Panics
    /// Panics if the starting point is greater than the end point, if the end
    /// point is greater than the length of the `String`, if either one does
    /// not lie on a [`char`] boundary, or if the remaining space is insufficient.
    pub fn extend_from_within<R: RangeBounds<usize>>(&mut self, src: R) {
        self.try_extend_from_within(src).expect("space remaining in string is insufficient");
    }

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
    /// let mut s = coca::collections::InlineString::<4>::from_str("ab");
    /// 
    /// assert!(s.try_push('c').is_ok());
    /// assert!(s.try_push('d').is_ok());
    /// assert!(s.try_push('e').is_err());
    /// 
    /// assert_eq!(s, "abcd");
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
    /// let s = coca::collections::InlineString::<8>::from_str("hello");
    /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
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
    /// let mut s = coca::collections::InlineString::<8>::from_str("hello");
    /// 
    /// s.truncate(2);
    /// 
    /// assert_eq!(s, "he");
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
    /// let mut s = coca::collections::InlineString::<4>::from_str("foo");
    /// 
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('f'));
    /// 
    /// assert_eq!(s.pop(), None);
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
    /// let mut s = coca::collections::InlineString::<4>::from_str("foo");
    /// 
    /// assert_eq!(s.remove(0), 'f');
    /// assert_eq!(s.remove(1), 'o');
    /// assert_eq!(s.remove(0), 'o');
    /// 
    /// assert!(s.is_empty());
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

    /// Retains only the characters specified by the predicate.
    /// 
    /// In other words, removes all characters `c` such that `f(c)` returns `false`.
    /// This method operates in place, visiting each character exactly once in the
    /// original order, and preserves the order of the retained characters.
    /// 
    /// # Examples
    /// ```
    /// let mut s = coca::collections::InlineString::<12>::from_str("f_o_o_b_a_r");
    /// 
    /// s.retain(|ch| ch != '_');
    /// 
    /// assert_eq!(s, "foobar");
    /// ```
    /// Because the elements are visited exactly once in the original order,
    /// external state may be used to decide which characters to keep:
    /// ```
    /// let mut s = coca::collections::InlineString::<8>::from_str("abcde");
    /// let keep = [false, true, true, false, true];
    /// let mut iter = keep.iter();
    /// s.retain(|_| *iter.next().unwrap());
    /// assert_eq!(s, "bce");
    /// ```
    pub fn retain<F: FnMut(char) -> bool>(&mut self, mut f: F) {
        let len = self.len();
        let mut idx = 0;
        let mut deleted_bytes = 0;
        
        while idx < len {
            let ch = unsafe { self.get_unchecked(idx..len).chars().next().unwrap() };
            let ch_len = ch.len_utf8();

            if !f(ch) {
                deleted_bytes += ch_len;
            } else if deleted_bytes > 0 {
                unsafe {
                    let src_ptr = self.vec.as_ptr().add(idx);
                    let dst_ptr = self.vec.as_mut_ptr().add(idx - deleted_bytes);
                    core::ptr::copy(src_ptr, dst_ptr, ch_len);
                }
            }

            idx += ch_len;
        }

        unsafe { self.vec.set_len(I::from_usize(len - deleted_bytes)) };
    }
    
    /// Inserts a character into the `String` at a given byte position.
    /// 
    /// Returns [`Err`] if the remaining space is insufficient.
    /// 
    /// This is an *O*(*n*) operation as it requires copying every element in the buffer.
    /// 
    /// # Panics
    /// Panics if `idx` is larger than the `String`'s length, or if it does not lie
    /// on a [`char`] boundary.
    /// 
    /// # Examples
    /// ```
    /// let mut s = coca::collections::InlineString::<3>::new();
    /// 
    /// assert!(s.try_insert(0, 'o').is_ok());
    /// assert!(s.try_insert(1, 'o').is_ok());
    /// assert!(s.try_insert(0, 'f').is_ok());
    /// 
    /// assert!(s.try_insert(3, 'b').is_err());
    /// 
    /// assert_eq!(s, "foo");
    /// ```
    pub fn try_insert(&mut self, idx: usize, ch: char) -> Result<(), ()> {
        assert!(self.is_char_boundary(idx));
        let mut bits = [0; 4];
        let bits = ch.encode_utf8(&mut bits).as_bytes();
        self.vec.try_insert_slice(I::from_usize(idx), bits)
    }

    /// Inserts a character into the `String` at a given byte position.
    /// 
    /// This is an *O*(*n*) operation as it requires copying every element in the buffer.
    /// 
    /// # Panics
    /// Panics if `idx` is larger than the `String`'s length, if it does not lie
    /// on a [`char`] boundary, or if the remaining space is insufficient.
    pub fn insert(&mut self, idx: usize, ch: char) {
        self.try_insert(idx, ch).expect("remaining space is insufficient");
    }

    /// Inserts a string slice into the `String` at a given byte position.
    /// 
    /// Returns [`Err`] if the remaining space is insufficient.
    /// 
    /// This is an *O*(*n*) operation as it requires copying every element in the buffer.
    /// 
    /// # Panics
    /// Panics if `idx` is larger than the `String`'s length, or if it does not
    /// lie on a [`char`] boundary.
    /// 
    /// # Examples
    /// ```
    /// let mut s = coca::collections::InlineString::<8>::from_str("bar");
    /// 
    /// assert!(s.try_insert_str(0, "foo").is_ok());
    /// assert!(s.try_insert_str(6, "bazz").is_err());
    /// 
    /// assert_eq!(s, "foobar");
    /// ```
    pub fn try_insert_str(&mut self, idx: usize, string: &str) -> Result<(), ()> {
        assert!(self.is_char_boundary(idx));
        self.vec.try_insert_slice(I::from_usize(idx), string.as_bytes())
    }

    /// Inserts a string slice into the `String` at a given byte position.
    /// 
    /// This is an *O*(*n*) operation as it requires copying every element in the buffer.
    /// 
    /// # Panics
    /// Panics if `idx` is larger than the `String`'s length, if it does not
    /// lie on a [`char`] boundary, or if the remaining space is insufficient.
    pub fn insert_str(&mut self, idx: usize, string: &str) {
        self.try_insert_str(idx, string).expect("remaining space is insufficient");
    }

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
    /// let mut s = coca::collections::InlineString::<8>::from_str("hello");
    /// 
    /// unsafe {
    ///     let mut vec = s.as_mut_vec();
    ///     assert_eq!(&[104, 101, 108, 108, 111][..], &vec[..]);
    ///     
    ///     vec.iter_mut().for_each(|b| *b += 1);
    /// }
    /// 
    /// assert_eq!(s, "ifmmp");
    /// ```
    #[inline]
    pub unsafe fn as_mut_vec(&mut self) -> &mut Vec<u8, S, I> {
        &mut self.vec
    }
    
    /// Creates a draining iterator that removes the specified range from the `String`
    /// and yields the removed [`char`]s.
    /// 
    /// Note: No matter how many elements of the iterator are consumed,
    /// the full range is removed when the iterator **is** dropped;
    /// if the iterator **is not** dropped, the `String` remains unchanged.
    /// 
    /// # Panics
    /// Panics if the starting point is greater than the end point, if the end
    /// point is greater than the length of the `String`, or if either one does
    /// not lie on a [`char`] boundary.
    /// 
    /// # Examples
    /// ```
    /// let mut s = coca::collections::InlineString::<32>::from_str("α is alpha, β is beta");
    /// let beta_offset = s.find('β').unwrap();
    /// 
    /// let mut drain_iter = s.drain(..beta_offset);
    /// assert_eq!(drain_iter.next(), Some('α'));
    /// assert_eq!(drain_iter.next_back(), Some(' '));
    /// 
    /// drop(drain_iter);
    /// assert_eq!(s, "β is beta");
    /// 
    /// s.drain(..);
    /// assert!(s.is_empty());
    /// ```
    pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> Drain<'_, S, I> {
        let Range { start, end } = normalize_range(range, self.len());
        assert!(self.is_char_boundary(start));
        assert!(self.is_char_boundary(end));
        let target_range = I::from_usize(start)..I::from_usize(end);
        
        let self_ptr = self as *mut _;
        let iter = unsafe { self.get_unchecked(start..end) }.chars();

        Drain { parent: self_ptr, target_range, iter }
    }
    
    /// Removes the specified range in the `String` and replaces it with the given string.
    /// The given string doesn't need to be the same length as the range.
    /// 
    /// Returns [`Err`] if the remaining space is insufficient.
    /// 
    /// # Panics
    /// Panics if the starting point is greater than the end point, if the end
    /// point is greater than the length of the `String`, or if either one does
    /// not lie on a [`char`] boundary.
    /// 
    /// # Examples
    /// ```
    /// let mut s = coca::collections::InlineString::<32>::from_str("α is alpha, β is beta");
    /// let beta_offset = s.find('β').unwrap();
    /// 
    /// assert!(s.try_replace_range(..beta_offset, "A is capital alpha; ").is_ok());
    /// assert_eq!(s, "A is capital alpha; β is beta");
    /// 
    /// let beta_offset = s.find('β').unwrap();
    /// assert!(s.try_replace_range(beta_offset.., "B is capital beta.").is_err());
    /// ```
    pub fn try_replace_range<R: RangeBounds<usize>>(&mut self, range: R, replace_with: &str) -> Result<(), ()> {
        let Range { start, end } = normalize_range(range, self.len());

        assert!(self.is_char_boundary(start));
        assert!(self.is_char_boundary(end));

        let range = I::from_usize(start)..I::from_usize(end);
        self.vec.try_replace_range(range, replace_with.as_bytes())
    }

    /// Removes the specified range in the `String` and replaces it with the given string.
    /// The given string doesn't need to be the same length as the range.
    /// 
    /// # Panics
    /// Panics if the starting point is greater than the end point, if the end
    /// point is greater than the length of the `String`, if either one does
    /// not lie on a [`char`] boundary, or if the remaining space is insufficient.
    pub fn replace_range<R: RangeBounds<usize>>(&mut self, range: R, replace_with: &str) {
        self.try_replace_range(range, replace_with).expect("remaining space is insufficient");
    }
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

impl<'a, I: Capacity> crate::collections::ArenaString<'a, I> {
    /// Converts the given boxed `str` slice into a `String`.
    /// 
    /// # Examples
    /// ```
    /// use coca::arena::Arena;
    /// use core::mem::MaybeUninit;
    ///
    /// # fn test() -> Option<()> {
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from(&mut backing_region[..]);
    /// 
    /// let boxed_str = coca::fmt!(arena, "{}", 1234567890)?;
    /// let mut string = coca::collections::ArenaString::<'_, usize>::from_boxed_str(boxed_str);
    /// 
    /// string.retain(|c| (c as u8) % 2 == 1);
    /// assert_eq!(string, "13579");
    /// # Some(()) }
    /// # assert!(test().is_some());
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
    /// use coca::arena::Arena;
    /// use core::mem::MaybeUninit;
    ///
    /// # fn test() -> Option<()> {
    /// let mut backing_region = [MaybeUninit::uninit(); 1024];
    /// let mut arena = Arena::from(&mut backing_region[..]);
    /// 
    /// let mut string = arena.string_with_capacity_from(16usize, "Hello, ");
    /// string.push('W');
    /// string.push_str("orld!");
    /// 
    /// let boxed_str = string.into_boxed_str();
    /// assert_eq!(boxed_str.as_ref(), "Hello, World!");
    /// # Some(()) }
    /// # assert!(test().is_some());
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
impl<I: Capacity> String<crate::storage::AllocStorage<ArrayLike<u8>>, I> {
    /// Creates a new, empty `AllocString` with the specified capacity.
    pub fn with_capacity(capacity: I) -> Self {
        Self::from(crate::storage::AllocStorage::with_capacity(capacity.as_usize()))
    }

    /// Creates a new `AllocString` with the given contents, and zero excess capacity.
    /// 
    /// # Examples
    /// ```
    /// let s = coca::collections::AllocString::<usize>::from_str("abcde");
    /// assert_eq!(s.capacity(), s.len());
    /// ```
    pub fn from_str(string: &str) -> Self {
        let mut buf = Self::with_capacity(I::from_usize(string.len()));
        buf.push_str(string);
        buf
    }

    /// Creates a new `AllocString` with the given capacity, and initializes it with the given content.
    /// 
    /// Returns [`Err`] if the given string is longer (in bytes) than `capacity`.
    /// 
    /// # Examples
    /// ```
    /// let s = coca::collections::AllocString::try_from_str_with_capacity("abcde", 8usize).unwrap();
    /// assert_eq!(s.capacity(), 8);
    /// assert_eq!(s, "abcde");
    /// 
    /// assert!(coca::collections::AllocString::try_from_str_with_capacity("abcde", 4usize).is_err());
    /// ```
    pub fn try_from_str_with_capacity(string: &str, capacity: I) -> Result<Self, ()> {
        let cap = capacity.as_usize();
        if string.len() > cap { return Err(()); }

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
    pub fn from_str_with_capacity(string: &str, capacity: I) -> Self {
        Self::try_from_str_with_capacity(string, capacity).expect("given string is longer than capacity")
    }
}

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
    /// let s = coca::collections::InlineString::<8>::try_from_str("abcde").unwrap();
    /// assert_eq!(s.capacity(), 8);
    /// assert_eq!(s, "abcde");
    /// 
    /// assert!(coca::collections::InlineString::<4>::try_from_str("abcde").is_err());
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

/// A draining iterator for [`String`].
/// 
/// This struct is created by the [`drain`](String::drain) method on `String`.
/// See its documentation for more.
pub struct Drain<'a, S: Storage<ArrayLike<u8>>, I: Capacity> {
    parent: *mut String<S, I>,
    target_range: Range<I>,
    iter: str::Chars<'a>,
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> Drain<'_, S, I> {
    /// Returns the remaining (sub)string of this iterator as a slice.
    pub fn as_str(&self) -> &str {
        self.iter.as_str()
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> fmt::Debug for Drain<'_, S, I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain").field(&self.as_str()).finish()
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> AsRef<str> for Drain<'_, S, I> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> AsRef<[u8]> for Drain<'_, S, I> {
    fn as_ref(&self) -> &[u8] {
        self.iter.as_str().as_bytes()
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> Iterator for Drain<'_, S, I> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<char> {
        self.next_back()
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> DoubleEndedIterator for Drain<'_, S, I> {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        self.iter.next_back()
    }
}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> core::iter::FusedIterator for Drain<'_, S, I> {}

impl<S: Storage<ArrayLike<u8>>, I: Capacity> Drop for Drain<'_, S, I> {
    fn drop(&mut self) {
        unsafe {
            let vec = (*self.parent).as_mut_vec();
            vec.drain(self.target_range.clone());
        }
    }
}