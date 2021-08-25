//! Groups of [`Option`](core::option::Option)s with bit-packed discriminants.
//! 
//! This is useful for optimizing the size of structs with multiple optional
//! fields that would otherwise be larger than the unwrapped equivalents
//! (see [the `core` module documentation](https://doc.rust-lang.org/core/option/#representation)
//! for more on this).
//! 
//! The [`OptionGroup`] struct is generic over two types:
//! 
//! * The flag set type `F` determines the maximum size of the group.
//!   Type aliases are provided for all common choices: [`OptionGroup8`],
//!   [`OptionGroup16`], [`OptionGroup32`] and [`OptionGroup64`].
//! * The compound type `T` must be either an array type or a tuple type.
//!   This is used to specify the types of the grouped values, and different
//!   associated functions are available depending on which of these modes
//!   is chosen.
//! 
//! # Examples
//! 
//! Tuples with 2 to 12 components may be used to define groups of values with
//! mixed types:
//! 
//! ```
//! # use coca::option_group::OptionGroup8;
//! let mut four_options: OptionGroup8<(u32, i16, u8, i8)> = OptionGroup8::empty();
//! assert!(four_options.is_empty());
//! 
//! assert_eq!(four_options.replace_0(0xC0FFE), None);
//! assert_eq!(four_options.replace_1(-1337), None);
//! 
//! assert_eq!(four_options.get_0(), Some(&0xC0FFE));
//! assert_eq!(four_options.get_1(), Some(&-1337));
//! assert!(four_options.get_2().is_none());
//! assert!(four_options.get_3().is_none());
//! 
//! if let Some(snd) = four_options.get_mut_1() {
//!     *snd = 1234;
//! }
//! 
//! assert_eq!(four_options.get_1(), Some(&1234));
//! ```
//! 
//! Arrays can be used to define homogeneous groups. A smaller, more flexible
//! API is provided for these:
//! 
//! ```
//! # use coca::option_group::OptionGroup32;
//! let mut many_options: OptionGroup32<[usize; 20]> = OptionGroup32::empty();
//! for i in 0..20 {
//!     if i % 7 < 3 { many_options.replace(i, 20 - i); }
//! }
//! 
//! assert_eq!(many_options.get(0), Some(&20));
//! assert!(many_options.get(5).is_none());
//! assert!(many_options.get(10).is_none());
//! assert_eq!(many_options.get(15), Some(&5));
//! ```

// TODO: for the array versions, implement iterators
//  -> it's unclear what these should look like exactly...
//  -> iterate over just the Some values, or should the Iterator<Item = Option<...>>?
//  -> if the former, should the Item type include the index? this is kind of a map-like data structure
//  => for now, just start with methods {first, next, prev, last}_{some, none} that return indices;
//     those should make a fine basis for any ad-hoc iteration scheme
// TODO: write more tests to run with miri

use core::mem::MaybeUninit;
use private::Compound;

/// Types that can be used as a flag set.
pub trait Flags: Copy + Into<u64> {
    /// The default value with no flags set.
    const ZERO: Self;
    /// Returns true if the *n*th flag is set.
    fn is_set(&self, n: u32) -> bool;
    /// Returns true if the *n*th flag is **not** set.
    #[inline(always)]
    fn is_clear(&self, n: u32) -> bool {
        !self.is_set(n)
    }
    /// Sets the *n*th flag.
    fn set(&mut self, n: u32);
    /// Clears the *n*th flag.
    fn clear(&mut self, n: u32);
}

macro_rules! impl_flags_trait {
    ($($t:ty),*) => {
        $(impl Flags for $t {
            const ZERO: Self = 0;
            #[inline(always)]
            fn is_set(&self, n: u32) -> bool {
                *self & (1 << n) != 0
            }
            #[inline(always)]
            fn set(&mut self, n: u32) {
                *self |= 1 << n;
            }
            #[inline(always)]
            fn clear(&mut self, n: u32) {
                *self &= !(1 << n);
            }
        })*
    };
}

impl_flags_trait!(u8, u16, u32, u64);

mod private {
    use core::mem::MaybeUninit;
    use core::ptr::{addr_of, addr_of_mut, null, null_mut};

    pub trait Compound: Sized {
        fn get_ptr(this: &MaybeUninit<Self>, idx: usize) -> *const ();
        fn get_mut_ptr(this: &mut MaybeUninit<Self>, idx: usize) -> *mut ();
        unsafe fn drop_all_in_place(this: &mut MaybeUninit<Self>, flags: u64);
    }

    macro_rules! impl_compound_for_tuple {
        ($cap:literal ; $($idx:tt : $t:ident),*) => {
            impl<$($t),*> Compound for ($($t),*) {
                #[inline(always)]
                fn get_ptr(this: &MaybeUninit<Self>, idx: usize) -> *const () {
                    match idx {
                        $($idx => unsafe { addr_of!((*this.as_ptr()).$idx) as _ }),*
                        _ => null(),
                    }
                }
                #[inline(always)]
                fn get_mut_ptr(this: &mut MaybeUninit<Self>, idx: usize) -> *mut () {
                    match idx {
                        $($idx => unsafe { addr_of_mut!((*this.as_mut_ptr()).$idx) as _ }),*
                        _ => null_mut(),
                    }
                }
                #[inline(always)]
                #[allow(unused_assignments)]
                unsafe fn drop_all_in_place(this: &mut MaybeUninit<Self>, flags: u64) {
                    let mut mask = 1;
                    $(
                        if flags & mask != 0 { (Self::get_mut_ptr(this, $idx) as *mut $t).drop_in_place(); }
                        mask <<= 1;
                    )*
                }
            }
        }
    }

    impl_compound_for_tuple!(2; 0: A, 1: B);
    impl_compound_for_tuple!(3; 0: A, 1: B, 2: C);
    impl_compound_for_tuple!(4; 0: A, 1: B, 2: C, 3: D);
    impl_compound_for_tuple!(5; 0: A, 1: B, 2: C, 3: D, 4: E);
    impl_compound_for_tuple!(6; 0: A, 1: B, 2: C, 3: D, 4: E, 5: F);
    impl_compound_for_tuple!(7; 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G);
    impl_compound_for_tuple!(8; 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H);
    impl_compound_for_tuple!(9; 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I);
    impl_compound_for_tuple!(10; 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I, 9: J);
    impl_compound_for_tuple!(11; 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I, 9: J, 10: K);
    impl_compound_for_tuple!(12; 0: A, 1: B, 2: C, 3: D, 4: E, 5: F, 6: G, 7: H, 8: I, 9: J, 10: K, 11: L);

    impl<T, const N: usize> Compound for [T; N] {
        #[inline(always)]
        fn get_ptr(this: &MaybeUninit<Self>, idx: usize) -> *const () {
            (this.as_ptr().cast::<T>()).wrapping_add(idx).cast()
        }
        #[inline(always)]
        fn get_mut_ptr(this: &mut MaybeUninit<Self>, idx: usize) -> *mut () {
            (this.as_mut_ptr().cast::<T>()).wrapping_add(idx).cast()
        }
        #[inline(always)]
        unsafe fn drop_all_in_place(this: &mut MaybeUninit<Self>, flags: u64) {
            for idx in 0..N {
                if flags & (1 << idx) != 0 { Self::get_mut_ptr(this, idx).drop_in_place(); }
            }
        }
    }
}

/// Types that can be represented as an `OptionGroup` with flag type `F`.
pub trait Representable<F: Flags> : Compound {}

impl<A, B> Representable<u8> for (A, B) {}
impl<A, B, C> Representable<u8> for (A, B, C) {}
impl<A, B, C, D> Representable<u8> for (A, B, C, D) {}
impl<A, B, C, D, E> Representable<u8> for (A, B, C, D, E) {}
impl<A, B, C, D, E, F> Representable<u8> for (A, B, C, D, E, F) {}
impl<A, B, C, D, E, F, G> Representable<u8> for (A, B, C, D, E, F, G) {}
impl<A, B, C, D, E, F, G, H> Representable<u8> for (A, B, C, D, E, F, G, H) {}
impl<A, B, C, D, E, F, G, H, I> Representable<u16> for (A, B, C, D, E, F, G, H, I) {}
impl<A, B, C, D, E, F, G, H, I, J> Representable<u16> for (A, B, C, D, E, F, G, H, I, J) {}
impl<A, B, C, D, E, F, G, H, I, J, K> Representable<u16> for (A, B, C, D, E, F, G, H, I, J, K) {}
impl<A, B, C, D, E, F, G, H, I, J, K, L> Representable<u16> for (A, B, C, D, E, F, G, H, I, J, K, L) {}

macro_rules! impl_marker_trait_for_arrays {
    ($traitname:ident < $param:ident > for [$($cap:literal),*]) => {
        $(impl<T> $traitname < $param > for [T; $cap] {})*
    }
}

impl_marker_trait_for_arrays!(Representable<u8> for [2, 3, 4, 5, 6, 7, 8]);
impl_marker_trait_for_arrays!(Representable<u16> for [9, 10, 11, 12, 13, 14, 15, 16]);
impl_marker_trait_for_arrays!(Representable<u32> for [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]);
impl_marker_trait_for_arrays!(Representable<u64> for [
    33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64
]);

impl<S> Representable<u16> for S where S: Representable<u8> {}
impl<S> Representable<u32> for S where S: Representable<u16> {}
impl<S> Representable<u64> for S where S: Representable<u32> {}

/// A group of multiple [`Option`]s with bit-packed discriminants.
/// 
/// Generic over the compound type `T` and the flags type `F`.
/// 
/// See the [module-level documentation](crate::option_group) for more.
pub struct OptionGroup<F, T> where F: Flags, T: Representable<F> {
    value: MaybeUninit<T>,
    flags: F,
}

/// A group of up to eight [`Option`]s with the discriminants packed into a single `u8`.
pub type OptionGroup8<T> = OptionGroup<u8, T>;
/// A group of up to sixteen [`Option`]s with the discriminants packed into a single `u16`.
pub type OptionGroup16<T> = OptionGroup<u16, T>;
/// A group of up to 32 [`Option`]s with the discriminants packed into a single `u32`.
pub type OptionGroup32<T> = OptionGroup<u32, T>;
/// A group of up to 64 [`Option`]s with the discriminants packed into a single `u64`.
pub type OptionGroup64<T> = OptionGroup<u64, T>;

impl<F, T> OptionGroup<F, T> where F: Flags, T: Representable<F> {
    /// Creates a new group with all options set to `None`.
    #[inline(always)]
    pub fn empty() -> Self {
        Self {
            value: MaybeUninit::uninit(),
            flags: F::ZERO,
        }
    }

    /// Returns `true` if all options in the group are `None` values.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.flags.into() == 0
    }

    /// Returns `true` if the *n*th option in the group is a `Some` value.
    #[inline(always)]
    pub fn is_some(&self, n: u32) -> bool {
        self.flags.is_set(n)
    }

    /// Returns `true` if the *n*th option in the group is a `None` value.
    #[inline(always)]
    pub fn is_none(&self, n: u32) -> bool {
        self.flags.is_clear(n)
    }
}

impl<F, T> Default for OptionGroup<F, T> where F: Flags, T: Representable<F> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<F, T> Drop for OptionGroup<F, T> where F: Flags, T: Representable<F> {
    fn drop(&mut self) {
        unsafe { T::drop_all_in_place(&mut self.value, self.flags.into()); }
    }
}

#[cold]
#[inline(never)]
fn index_out_of_bounds(index: usize, len: usize) -> ! {
    panic!(
        "idx (is {}) should be <= N (is {})",
        index, len
    );
}

impl<F, T, const N: usize> OptionGroup<F, [T; N]> where F: Flags, [T; N]: Representable<F> {
    /// Creates a new `OptionGroup` initialized with the provided values.
    pub fn new(values: [Option<T>; N]) -> Self {
        let mut result = Self::empty();
        for (idx, v) in core::array::IntoIter::new(values).enumerate() {
            if let Some(value) = v {
                result.replace(idx, value);
            }
        }

        result
    }

    /// Equivalent to [`array_of_options[idx].as_ref()`](core::option::Option::as_ref).
    /// 
    /// # Panics
    /// Panics if `idx >= N`.
    #[inline(always)]
    pub fn get(&self, idx: usize) -> Option<&T> {
        if idx >= N {
            index_out_of_bounds(idx, N);
        }

        #[allow(clippy::cast_possible_truncation)]
        if self.flags.is_clear(idx as u32) {
            return None;
        }

        unsafe {
            (<[T; N] as Compound>::get_ptr(&self.value, idx).cast::<T>()).as_ref()
        }
    }

    /// Equivalent to [`array_of_options[idx].as_mut()`](core::option::Option::as_ref).
    /// 
    /// # Panics
    /// Panics if `idx >= N`.
    #[inline(always)]
    pub fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
        if idx >= N {
            index_out_of_bounds(idx, N);
        }

        #[allow(clippy::cast_possible_truncation)]
        if self.flags.is_clear(idx as u32) {
            return None;
        }

        unsafe { Some(self.get_mut_unchecked(idx)) }
    }

    /// Returns a mutable reference to the `Some` value at position
    /// `idx`, without checking that `idx` is in bounds or that the
    /// value is not `None`.
    /// 
    /// # Safety
    /// Calling this method with `idx >= N` or when the value at that
    /// position is `None` is undefined behavior.
    #[inline(always)]
    pub unsafe fn get_mut_unchecked(&mut self, idx: usize) -> &mut T {
        &mut *(<[T; N] as Compound>::get_mut_ptr(&mut self.value, idx).cast::<T>())
    }

    /// Equivalent to [`array_of_options[idx].insert(value)`](core::option::Option::insert).
    /// 
    /// # Panics
    /// Panics if `idx >= N`.
    #[inline(always)]
    pub fn insert(&mut self, idx: usize, value: T) -> &mut T {
        self.replace(idx, value);
        unsafe { self.get_mut_unchecked(idx) }
    }

    /// Equivalent to [`array_of_options[idx].get_or_insert(value)`](core::option::Option::get_or_insert).
    /// 
    /// # Panics
    /// Panics if `idx >= N`.
    #[inline(always)]
    pub fn get_or_insert(&mut self, idx: usize, value: T) -> &mut T {
        if idx >= N {
            index_out_of_bounds(idx, N);
        }

        #[allow(clippy::cast_possible_truncation)]
        if self.is_none(idx as u32) {
            self.replace(idx, value);
        }

        unsafe { self.get_mut_unchecked(idx) }
    }

    /// Equivalent to [`array_of_options[idx].get_or_insert_with(f)`](core::option::Option::get_or_insert_with).
    /// 
    /// # Panics
    /// Panics if `idx >= N`.
    #[inline(always)]
    pub fn get_or_insert_with<FN: FnOnce() -> T>(&mut self, idx: usize, f: FN) -> &mut T {
        if idx >= N {
            index_out_of_bounds(idx, N);
        }

        #[allow(clippy::cast_possible_truncation)]
        if self.is_none(idx as u32) {
            self.replace(idx, f());
        }

        unsafe { self.get_mut_unchecked(idx) }
    }

    /// Equivalent to [`array_of_options[idx].take()`](core::option::Option::take).
    /// 
    /// # Panics
    /// Panics if `idx >= N`.
    #[inline(always)]
    pub fn take(&mut self, idx: usize) -> Option<T> {
        if idx >= N {
            index_out_of_bounds(idx, N);
        }

        #[allow(clippy::cast_possible_truncation)]
        if self.is_some(idx as u32) {
            self.flags.clear(idx as u32);
            Some(unsafe {
                (<[T; N] as Compound>::get_ptr(&self.value, idx).cast::<T>()).read()
            })
        } else {
            None
        }
    }

    /// Equivalent to [`array_of_options[idx].replace(value)`](core::option::Option::replace).
    /// 
    /// # Panics
    /// Panics if `idx >= N`.
    #[inline(always)]
    pub fn replace(&mut self, idx: usize, value: T) -> Option<T> {
        let result = self.take(idx);

        #[allow(clippy::cast_possible_truncation)]
        self.flags.set(idx as u32);

        unsafe {
            (<[T; N] as Compound>::get_mut_ptr(&mut self.value, idx).cast::<T>()).write(value);
        }
        result
    }
}

/// Tuple types with a field of type `TX` at position `X`.
pub trait Tuple<const X: usize> : Compound {
    /// The type of the field at position `X`.
    type TX;
}

macro_rules! impl_tuple_traits {
    ( $($typenames:ident),* : $($traitparams:literal),* ) => {
        impl_tuple_traits_helper_1!(
            ( $($typenames),* ) : ( $($traitparams),* ) ( $($typenames),* )
        );
    }
}

macro_rules! impl_tuple_traits_helper_1 {
    ( $ts:tt : ( $($traitparam:literal),* ) ( $($t:ident),* ) ) => {
        impl_tuple_traits_helper_2!(
            $( [ $ts : $traitparam $t ] )*
        );
    }
}

macro_rules! impl_tuple_traits_helper_2 {
    ( $( [ ( $($ts:ident),* ) : $traitparam:literal $t:ident ] )* ) => {
        $(impl<$($ts),*> Tuple<$traitparam> for ( $($ts),* ) { type TX = $t; } )*
    }
}

impl_tuple_traits!(A, B : 0, 1);
impl_tuple_traits!(A, B, C : 0, 1, 2);
impl_tuple_traits!(A, B, C, D : 0, 1, 2, 3);
impl_tuple_traits!(A, B, C, D, E : 0, 1, 2, 3, 4);
impl_tuple_traits!(A, B, C, D, E, F : 0, 1, 2, 3, 4, 5);
impl_tuple_traits!(A, B, C, D, E, F, G : 0, 1, 2, 3, 4, 5, 6);
impl_tuple_traits!(A, B, C, D, E, F, G, H : 0, 1, 2, 3, 4, 5, 6, 7);
impl_tuple_traits!(A, B, C, D, E, F, G, H, I : 0, 1, 2, 3, 4, 5, 6, 7, 8);
impl_tuple_traits!(A, B, C, D, E, F, G, H, I, J : 0, 1, 2, 3, 4, 5, 6, 7, 8, 9);
impl_tuple_traits!(A, B, C, D, E, F, G, H, I, J, K : 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
impl_tuple_traits!(A, B, C, D, E, F, G, H, I, J, K, L : 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11);

macro_rules! impl_tuple_accessors {
    ($idx:literal, $get:ident, $get_mut:ident, $get_mut_unchecked:ident, $insert:ident, $get_or_insert:ident, $get_or_insert_with:ident, $take:ident, $replace:ident) => {
        impl<F, T> OptionGroup<F, T> where F: Flags, T: Representable<F> + Tuple<$idx> {
            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".as_ref()`](core::option::Option::as_ref).")]
            #[inline(always)]
            pub fn $get(&self) -> Option<& <T as Tuple<$idx>>::TX> {
                if self.is_none($idx) {
                    None
                } else {
                    unsafe { (<T as Compound>::get_ptr(&self.value, $idx) as *const <T as Tuple<$idx>>::TX).as_ref() }
                }
            }

            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".as_mut()`](core::option::Option::as_mut).")]
            #[inline(always)]
            pub fn $get_mut(&mut self) -> Option<&mut <T as Tuple<$idx>>::TX> {
                if self.is_none($idx) {
                    None
                } else {
                    unsafe { Some(self.$get_mut_unchecked()) }
                }
            }

            #[doc = concat!(" Returns a mutable reference to the `Some` value at position ", $idx, ", without checking that the value is not `None`.")]
            #[doc = " # Safety"]
            #[doc = " Calling this method on `None` is undefined behavior."]
            #[inline(always)]
            pub unsafe fn $get_mut_unchecked(&mut self) -> &mut <T as Tuple<$idx>>::TX {
                &mut *(<T as Compound>::get_mut_ptr(&mut self.value, $idx) as *mut <T as Tuple<$idx>>::TX)
            }

            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".insert(value)`](core::option::Option::insert).")]
            #[inline(always)]
            pub fn $insert(&mut self, value: <T as Tuple<$idx>>::TX) -> &mut <T as Tuple<$idx>>::TX {
                self.$replace(value);
                unsafe { self.$get_mut_unchecked() }
            }

            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".get_or_insert(value)`](core::option::Option::get_or_insert).")]
            #[inline(always)]
            pub fn $get_or_insert(&mut self, value: <T as Tuple<$idx>>::TX) -> &mut <T as Tuple<$idx>>::TX {
                if self.is_none($idx) {
                    self.$replace(value);
                }
                unsafe { self.$get_mut_unchecked() }
            }

            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".get_or_insert_with(f)`](core::option::Option::get_or_insert_with).")]
            #[inline(always)]
            pub fn $get_or_insert_with<FN: FnOnce() -> <T as Tuple<$idx>>::TX>(&mut self, f: FN) -> &mut <T as Tuple<$idx>>::TX {
                if self.is_none($idx) {
                    self.$replace(f());
                }
                unsafe { self.$get_mut_unchecked() }
            }

            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".take()`](core::option::Option::take).")]
            #[inline(always)]
            pub fn $take(&mut self) -> Option<<T as Tuple<$idx>>::TX> {
                if self.is_none($idx) {
                    None
                } else {
                    self.flags.clear($idx);
                    unsafe { Some((<T as Compound>::get_ptr(&self.value, $idx) as *const <T as Tuple<$idx>>::TX).read()) }
                }
            }

            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".replace(value)`](core::option::Option::replace).")]
            #[inline(always)]
            pub fn $replace(&mut self, value: <T as Tuple<$idx>>::TX) -> Option<<T as Tuple<$idx>>::TX> {
                let result = self.$take();
                unsafe { (<T as Compound>::get_mut_ptr(&mut self.value, $idx) as *mut <T as Tuple<$idx>>::TX ).write(value) };
                self.flags.set($idx);
                result
            }
        }
    };
}

impl_tuple_accessors!(0, get_0, get_mut_0, get_mut_unchecked_0, insert_0, get_or_insert_0, get_or_insert_with_0, take_0, replace_0);
impl_tuple_accessors!(1, get_1, get_mut_1, get_mut_unchecked_1, insert_1, get_or_insert_1, get_or_insert_with_1, take_1, replace_1);
impl_tuple_accessors!(2, get_2, get_mut_2, get_mut_unchecked_2, insert_2, get_or_insert_2, get_or_insert_with_2, take_2, replace_2);
impl_tuple_accessors!(3, get_3, get_mut_3, get_mut_unchecked_3, insert_3, get_or_insert_3, get_or_insert_with_3, take_3, replace_3);
impl_tuple_accessors!(4, get_4, get_mut_4, get_mut_unchecked_4, insert_4, get_or_insert_4, get_or_insert_with_4, take_4, replace_4);
impl_tuple_accessors!(5, get_5, get_mut_5, get_mut_unchecked_5, insert_5, get_or_insert_5, get_or_insert_with_5, take_5, replace_5);
impl_tuple_accessors!(6, get_6, get_mut_6, get_mut_unchecked_6, insert_6, get_or_insert_6, get_or_insert_with_6, take_6, replace_6);
impl_tuple_accessors!(7, get_7, get_mut_7, get_mut_unchecked_7, insert_7, get_or_insert_7, get_or_insert_with_7, take_7, replace_7);
impl_tuple_accessors!(8, get_8, get_mut_8, get_mut_unchecked_8, insert_8, get_or_insert_8, get_or_insert_with_8, take_8, replace_8);
impl_tuple_accessors!(9, get_9, get_mut_9, get_mut_unchecked_9, insert_9, get_or_insert_9, get_or_insert_with_9, take_9, replace_9);
impl_tuple_accessors!(10, get_10, get_mut_10, get_mut_unchecked_10, insert_10, get_or_insert_10, get_or_insert_with_10, take_10, replace_10);
impl_tuple_accessors!(11, get_11, get_mut_11, get_mut_unchecked_11, insert_11, get_or_insert_11, get_or_insert_with_11, take_11, replace_11);
