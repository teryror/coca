//! Groups of [`Option`](std::option::Option) with packed discriminants.
//! 
//! This is useful for optimizing the size of structs with multiple optional
//! fields that would otherwise be larger than the unwrapped equivalents
//! (see [the `core` module documentation](https://doc.rust-lang.org/core/option/#representation)
//! for more on this).
//! 
//! This module exports multiple such types: [`OptionGroup8`], [`OptionGroup16`],
//! [`OptionGroup32`], and [`OptionGroup64`]. The only difference between these
//! is the size of the flag field, and thus their capacity.
//! 
//! For each group size, different associated functions are implemented depending
//! on the way in which the component types are specified.
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
// TODO: write more tests to run with miri

use core::mem::MaybeUninit;
use private::Compound;

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

macro_rules! define_tuple_trait {
    ($num:literal : $traitname:ident < $t:ident > : $supertrait:ident) => {
        #[doc = core::concat!("Tuples with more than ", $num, " element(s).")]
        pub trait $traitname : $supertrait {
            #[doc = core::concat!("The type of the element at position ", $num, ".")]
            type $t;
        }
    };
}

define_tuple_trait!(0 : Tuple0<T>: Compound);
impl<A, B> Tuple0 for (A, B) { type T = A; }
impl<A, B, C> Tuple0 for (A, B, C) { type T = A; }
impl<A, B, C, D> Tuple0 for (A, B, C, D) { type T = A; }
impl<A, B, C, D, E> Tuple0 for (A, B, C, D, E) { type T = A; }
impl<A, B, C, D, E, F> Tuple0 for (A, B, C, D, E, F) { type T = A; }
impl<A, B, C, D, E, F, G> Tuple0 for (A, B, C, D, E, F, G) { type T = A; }
impl<A, B, C, D, E, F, G, H> Tuple0 for (A, B, C, D, E, F, G, H) { type T = A; }
impl<A, B, C, D, E, F, G, H, I> Tuple0 for (A, B, C, D, E, F, G, H, I) { type T = A; }
impl<A, B, C, D, E, F, G, H, I, J> Tuple0 for (A, B, C, D, E, F, G, H, I, J) { type T = A; }
impl<A, B, C, D, E, F, G, H, I, J, K> Tuple0 for (A, B, C, D, E, F, G, H, I, J, K) { type T = A; }
impl<A, B, C, D, E, F, G, H, I, J, K, L> Tuple0 for (A, B, C, D, E, F, G, H, I, J, K, L) { type T = A; }

define_tuple_trait!(1 : Tuple1<T>: Tuple0);
impl<A, B> Tuple1 for (A, B) { type T = B; }
impl<A, B, C> Tuple1 for (A, B, C) { type T = B; }
impl<A, B, C, D> Tuple1 for (A, B, C, D) { type T = B; }
impl<A, B, C, D, E> Tuple1 for (A, B, C, D, E) { type T = B; }
impl<A, B, C, D, E, F> Tuple1 for (A, B, C, D, E, F) { type T = B; }
impl<A, B, C, D, E, F, G> Tuple1 for (A, B, C, D, E, F, G) { type T = B; }
impl<A, B, C, D, E, F, G, H> Tuple1 for (A, B, C, D, E, F, G, H) { type T = B; }
impl<A, B, C, D, E, F, G, H, I> Tuple1 for (A, B, C, D, E, F, G, H, I) { type T = B; }
impl<A, B, C, D, E, F, G, H, I, J> Tuple1 for (A, B, C, D, E, F, G, H, I, J) { type T = B; }
impl<A, B, C, D, E, F, G, H, I, J, K> Tuple1 for (A, B, C, D, E, F, G, H, I, J, K) { type T = B; }
impl<A, B, C, D, E, F, G, H, I, J, K, L> Tuple1 for (A, B, C, D, E, F, G, H, I, J, K, L) { type T = B; }

define_tuple_trait!(2 : Tuple2<T>: Tuple1);
impl<A, B, C> Tuple2 for (A, B, C) { type T = C; }
impl<A, B, C, D> Tuple2 for (A, B, C, D) { type T = C; }
impl<A, B, C, D, E> Tuple2 for (A, B, C, D, E) { type T = C; }
impl<A, B, C, D, E, F> Tuple2 for (A, B, C, D, E, F) { type T = C; }
impl<A, B, C, D, E, F, G> Tuple2 for (A, B, C, D, E, F, G) { type T = C; }
impl<A, B, C, D, E, F, G, H> Tuple2 for (A, B, C, D, E, F, G, H) { type T = C; }
impl<A, B, C, D, E, F, G, H, I> Tuple2 for (A, B, C, D, E, F, G, H, I) { type T = C; }
impl<A, B, C, D, E, F, G, H, I, J> Tuple2 for (A, B, C, D, E, F, G, H, I, J) { type T = C; }
impl<A, B, C, D, E, F, G, H, I, J, K> Tuple2 for (A, B, C, D, E, F, G, H, I, J, K) { type T = C; }
impl<A, B, C, D, E, F, G, H, I, J, K, L> Tuple2 for (A, B, C, D, E, F, G, H, I, J, K, L) { type T = C; }

define_tuple_trait!(3 : Tuple3<T>: Tuple2);
impl<A, B, C, D> Tuple3 for (A, B, C, D) { type T = D; }
impl<A, B, C, D, E> Tuple3 for (A, B, C, D, E) { type T = D; }
impl<A, B, C, D, E, F> Tuple3 for (A, B, C, D, E, F) { type T = D; }
impl<A, B, C, D, E, F, G> Tuple3 for (A, B, C, D, E, F, G) { type T = D; }
impl<A, B, C, D, E, F, G, H> Tuple3 for (A, B, C, D, E, F, G, H) { type T = D; }
impl<A, B, C, D, E, F, G, H, I> Tuple3 for (A, B, C, D, E, F, G, H, I) { type T = D; }
impl<A, B, C, D, E, F, G, H, I, J> Tuple3 for (A, B, C, D, E, F, G, H, I, J) { type T = D; }
impl<A, B, C, D, E, F, G, H, I, J, K> Tuple3 for (A, B, C, D, E, F, G, H, I, J, K) { type T = D; }
impl<A, B, C, D, E, F, G, H, I, J, K, L> Tuple3 for (A, B, C, D, E, F, G, H, I, J, K, L) { type T = D; }

define_tuple_trait!(4 : Tuple4<T>: Tuple3);
impl<A, B, C, D, E> Tuple4 for (A, B, C, D, E) { type T = E; }
impl<A, B, C, D, E, F> Tuple4 for (A, B, C, D, E, F) { type T = E; }
impl<A, B, C, D, E, F, G> Tuple4 for (A, B, C, D, E, F, G) { type T = E; }
impl<A, B, C, D, E, F, G, H> Tuple4 for (A, B, C, D, E, F, G, H) { type T = E; }
impl<A, B, C, D, E, F, G, H, I> Tuple4 for (A, B, C, D, E, F, G, H, I) { type T = E; }
impl<A, B, C, D, E, F, G, H, I, J> Tuple4 for (A, B, C, D, E, F, G, H, I, J) { type T = E; }
impl<A, B, C, D, E, F, G, H, I, J, K> Tuple4 for (A, B, C, D, E, F, G, H, I, J, K) { type T = E; }
impl<A, B, C, D, E, F, G, H, I, J, K, L> Tuple4 for (A, B, C, D, E, F, G, H, I, J, K, L) { type T = E; }

define_tuple_trait!(5 : Tuple5<T>: Tuple4);
impl<A, B, C, D, E, F> Tuple5 for (A, B, C, D, E, F) { type T = F; }
impl<A, B, C, D, E, F, G> Tuple5 for (A, B, C, D, E, F, G) { type T = F; }
impl<A, B, C, D, E, F, G, H> Tuple5 for (A, B, C, D, E, F, G, H) { type T = F; }
impl<A, B, C, D, E, F, G, H, I> Tuple5 for (A, B, C, D, E, F, G, H, I) { type T = F; }
impl<A, B, C, D, E, F, G, H, I, J> Tuple5 for (A, B, C, D, E, F, G, H, I, J) { type T = F; }
impl<A, B, C, D, E, F, G, H, I, J, K> Tuple5 for (A, B, C, D, E, F, G, H, I, J, K) { type T = F; }
impl<A, B, C, D, E, F, G, H, I, J, K, L> Tuple5 for (A, B, C, D, E, F, G, H, I, J, K, L) { type T = F; }

define_tuple_trait!(6 : Tuple6<T>: Tuple5);
impl<A, B, C, D, E, F, G> Tuple6 for (A, B, C, D, E, F, G) { type T = G; }
impl<A, B, C, D, E, F, G, H> Tuple6 for (A, B, C, D, E, F, G, H) { type T = G; }
impl<A, B, C, D, E, F, G, H, I> Tuple6 for (A, B, C, D, E, F, G, H, I) { type T = G; }
impl<A, B, C, D, E, F, G, H, I, J> Tuple6 for (A, B, C, D, E, F, G, H, I, J) { type T = G; }
impl<A, B, C, D, E, F, G, H, I, J, K> Tuple6 for (A, B, C, D, E, F, G, H, I, J, K) { type T = G; }
impl<A, B, C, D, E, F, G, H, I, J, K, L> Tuple6 for (A, B, C, D, E, F, G, H, I, J, K, L) { type T = G; }

define_tuple_trait!(7 : Tuple7<T>: Tuple6);
impl<A, B, C, D, E, F, G, H> Tuple7 for (A, B, C, D, E, F, G, H) { type T = H; }
impl<A, B, C, D, E, F, G, H, I> Tuple7 for (A, B, C, D, E, F, G, H, I) { type T = H; }
impl<A, B, C, D, E, F, G, H, I, J> Tuple7 for (A, B, C, D, E, F, G, H, I, J) { type T = H; }
impl<A, B, C, D, E, F, G, H, I, J, K> Tuple7 for (A, B, C, D, E, F, G, H, I, J, K) { type T = H; }
impl<A, B, C, D, E, F, G, H, I, J, K, L> Tuple7 for (A, B, C, D, E, F, G, H, I, J, K, L) { type T = H; }

define_tuple_trait!(8 : Tuple8<T>: Tuple7);
impl<A, B, C, D, E, F, G, H, I> Tuple8 for (A, B, C, D, E, F, G, H, I) { type T = I; }
impl<A, B, C, D, E, F, G, H, I, J> Tuple8 for (A, B, C, D, E, F, G, H, I, J) { type T = I; }
impl<A, B, C, D, E, F, G, H, I, J, K> Tuple8 for (A, B, C, D, E, F, G, H, I, J, K) { type T = I; }
impl<A, B, C, D, E, F, G, H, I, J, K, L> Tuple8 for (A, B, C, D, E, F, G, H, I, J, K, L) { type T = I; }

define_tuple_trait!(9 : Tuple9<T>: Tuple8);
impl<A, B, C, D, E, F, G, H, I, J> Tuple9 for (A, B, C, D, E, F, G, H, I, J) { type T = J; }
impl<A, B, C, D, E, F, G, H, I, J, K> Tuple9 for (A, B, C, D, E, F, G, H, I, J, K) { type T = J; }
impl<A, B, C, D, E, F, G, H, I, J, K, L> Tuple9 for (A, B, C, D, E, F, G, H, I, J, K, L) { type T = J; }

define_tuple_trait!(10 : Tuple10<T>: Tuple9);
impl<A, B, C, D, E, F, G, H, I, J, K> Tuple10 for (A, B, C, D, E, F, G, H, I, J, K) { type T = K; }
impl<A, B, C, D, E, F, G, H, I, J, K, L> Tuple10 for (A, B, C, D, E, F, G, H, I, J, K, L) { type T = K; }

define_tuple_trait!(11 : Tuple11<T>: Tuple10);
impl<A, B, C, D, E, F, G, H, I, J, K, L> Tuple11 for (A, B, C, D, E, F, G, H, I, J, K, L) { type T = L; }

/// Groups of up to eight values. Can be packed into an [`OptionGroup8`] or larger.
pub trait Compound8: Compound {}
impl<A, B> Compound8 for (A, B) {}
impl<A, B, C> Compound8 for (A, B, C) {}
impl<A, B, C, D> Compound8 for (A, B, C, D) {}
impl<A, B, C, D, E> Compound8 for (A, B, C, D, E) {}
impl<A, B, C, D, E, F> Compound8 for (A, B, C, D, E, F) {}
impl<A, B, C, D, E, F, G> Compound8 for (A, B, C, D, E, F, G) {}
impl<A, B, C, D, E, F, G, H> Compound8 for (A, B, C, D, E, F, G, H) {}

macro_rules! impl_marker_trait_for_arrays {
    ($traitname:ident for [$($cap:literal),*]) => {
        $(impl<T> $traitname for [T; $cap] {})*
    }
}

impl_marker_trait_for_arrays!(Compound8 for [2, 3, 4, 5, 6, 7, 8]);

/// Groups of up to sixteen values. Can be packed into an [`OptionGroup16`] or larger.
pub trait Compound16: Compound {}
impl<C> Compound16 for C where C: Compound8 {}

impl<A, B, C, D, E, F, G, H, I> Compound16 for (A, B, C, D, E, F, G, H, I) {}
impl<A, B, C, D, E, F, G, H, I, J> Compound16 for (A, B, C, D, E, F, G, H, I, J) {}
impl<A, B, C, D, E, F, G, H, I, J, K> Compound16 for (A, B, C, D, E, F, G, H, I, J, K) {}
impl<A, B, C, D, E, F, G, H, I, J, K, L> Compound16 for (A, B, C, D, E, F, G, H, I, J, K, L) {}

impl_marker_trait_for_arrays!(Compound16 for [9, 10, 11, 12, 13, 14, 15, 16]);

/// Groups of up to 32 values. Can be packed into an [`OptionGroup32`] or larger.
pub trait Compound32: Compound {}
impl<C> Compound32 for C where C: Compound16 {}
impl_marker_trait_for_arrays!(Compound32 for [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]);

/// Groups of up to 64 values. Can be packed into an [`OptionGroup64`] or larger.
pub trait Compound64: Compound {}
impl<C> Compound64 for C where C: Compound32 {}
impl_marker_trait_for_arrays!(Compound64 for [
    33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64
]);

/// A group of up to eight [`Option`](core::option::Option)s, with the
/// discriminants packed into a single `u8`.
/// 
/// See the [module-level documentation](crate::option_group) for more.
pub struct OptionGroup8<T: Compound8> {
    value: MaybeUninit<T>,
    flags: u8,
}

macro_rules! impl_option_group {
    ($typename:ident, $traitname:ident) => {
        impl<T> $typename<T> where T: $traitname {
            /// Creates a new group with all options set to `None`.
            #[inline(always)]
            pub fn empty() -> Self {
                Self {
                    value: MaybeUninit::uninit(),
                    flags: 0,
                }
            }

            #[inline(always)]
            fn set_flag(&mut self, n: u32) {
                self.flags |= 1 << n;
            }

            #[inline(always)]
            fn clear_flag(&mut self, n: u32) {
                self.flags &= !(1 << n);
            }

            /// Returns `true` if all options in the group are `None` values.
            #[inline(always)]
            pub fn is_empty(&self) -> bool {
                self.flags == 0
            }

            /// Returns `true` if the *n*th option in the group is a `Some` value.
            #[inline(always)]
            pub fn is_some(&self, n: u32) -> bool {
                self.flags & (1 << n) != 0
            }

            /// Returns `true` if the *n*th option in the group is a `None` value.
            #[inline(always)]
            pub fn is_none(&self, n: u32) -> bool {
                self.flags & (1 << n) == 0
            }
        }

        impl<T> Default for $typename<T> where T: $traitname {
            fn default() -> Self {
                Self::empty()
            }
        }

        impl<T> Drop for $typename<T> where T: $traitname {
            fn drop(&mut self) {
                unsafe { T::drop_all_in_place(&mut self.value, self.flags as u64); }
            }
        }
    };
}

impl_option_group!(OptionGroup8, Compound8);

macro_rules! impl_tuple_accessors {
    ($ogtype:ident < $compoundtrait:ident + $tupletrait:ident , $idx:literal > $get:ident, $get_mut:ident, $get_mut_unchecked:ident, $insert:ident, $get_or_insert:ident, $get_or_insert_with:ident, $take:ident, $replace:ident) => {
        impl<T> $ogtype <T> where T: $compoundtrait + $tupletrait {
            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".as_ref()`](core::option::Option::as_ref).")]
            #[inline(always)]
            pub fn $get(&self) -> Option<& <T as $tupletrait>::T> {
                if self.is_none($idx) {
                    None
                } else {
                    unsafe { (<T as Compound>::get_ptr(&self.value, $idx) as *const <T as $tupletrait>::T).as_ref() }
                }
            }

            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".as_mut()`](core::option::Option::as_mut).")]
            #[inline(always)]
            pub fn $get_mut(&mut self) -> Option<&mut <T as $tupletrait>::T> {
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
            pub unsafe fn $get_mut_unchecked(&mut self) -> &mut <T as $tupletrait>::T {
                &mut *(<T as Compound>::get_mut_ptr(&mut self.value, $idx) as *mut <T as $tupletrait>::T)
            }

            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".insert(value)`](core::option::Option::insert).")]
            #[inline(always)]
            pub fn $insert(&mut self, value: <T as $tupletrait>::T) -> &mut <T as $tupletrait>::T {
                self.$replace(value);
                unsafe { self.$get_mut_unchecked() }
            }

            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".get_or_insert(value)`](core::option::Option::get_or_insert).")]
            #[inline(always)]
            pub fn $get_or_insert(&mut self, value: <T as $tupletrait>::T) -> &mut <T as $tupletrait>::T {
                if self.is_none($idx) {
                    self.$replace(value);
                }
                unsafe { self.$get_mut_unchecked() }
            }

            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".get_or_insert_with(f)`](core::option::Option::get_or_insert_with).")]
            #[inline(always)]
            pub fn $get_or_insert_with<F: FnOnce() -> <T as $tupletrait>::T>(&mut self, f: F) -> &mut <T as $tupletrait>::T {
                if self.is_none($idx) {
                    self.$replace(f());
                }
                unsafe { self.$get_mut_unchecked() }
            }

            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".take()`](core::option::Option::take).")]
            #[inline(always)]
            pub fn $take(&mut self) -> Option<<T as $tupletrait>::T> {
                if self.is_none($idx) {
                    None
                } else {
                    self.clear_flag($idx);
                    unsafe { Some((<T as Compound>::get_ptr(&self.value, $idx) as *const <T as $tupletrait>::T).read()) }
                }
            }

            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".replace(value)`](core::option::Option::replace).")]
            #[inline(always)]
            pub fn $replace(&mut self, value: <T as $tupletrait>::T) -> Option<<T as $tupletrait>::T> {
                let result = self.$take();
                unsafe { (<T as Compound>::get_mut_ptr(&mut self.value, $idx) as *mut <T as $tupletrait>::T ).write(value) };
                self.set_flag($idx);
                result
            }
        }
    };
}

impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple0, 0> get_0, get_mut_0, get_mut_unchecked_0, insert_0, get_or_insert_0, get_or_insert_with_0, take_0, replace_0);
impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple1, 1> get_1, get_mut_1, get_mut_unchecked_1, insert_1, get_or_insert_1, get_or_insert_with_1, take_1, replace_1);
impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple2, 2> get_2, get_mut_2, get_mut_unchecked_2, insert_2, get_or_insert_2, get_or_insert_with_2, take_2, replace_2);
impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple3, 3> get_3, get_mut_3, get_mut_unchecked_3, insert_3, get_or_insert_3, get_or_insert_with_3, take_3, replace_3);
impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple4, 4> get_4, get_mut_4, get_mut_unchecked_4, insert_4, get_or_insert_4, get_or_insert_with_4, take_4, replace_4);
impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple5, 5> get_5, get_mut_5, get_mut_unchecked_5, insert_5, get_or_insert_5, get_or_insert_with_5, take_5, replace_5);
impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple6, 6> get_6, get_mut_6, get_mut_unchecked_6, insert_6, get_or_insert_6, get_or_insert_with_6, take_6, replace_6);
impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple7, 7> get_7, get_mut_7, get_mut_unchecked_7, insert_7, get_or_insert_7, get_or_insert_with_7, take_7, replace_7);

#[cold]
#[inline(never)]
fn index_out_of_bounds(index: usize, len: usize) -> ! {
    panic!(
        "idx (is {}) should be <= N (is {})",
        index, len
    );
}

macro_rules! impl_array_methods {
    ($typename:ident, $traitname:ident) => {
        impl<T, const N: usize> $typename<[T; N]> where [T; N]: $traitname {
            #[doc = concat!("Creates a new `", stringify!($typename), "<", stringify!([T; N]), ">` initialized with the provided values.")]
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

                if self.flags & (1 << idx) == 0 {
                    return None;
                }

                unsafe {
                    (<[T; N] as Compound>::get_ptr(&self.value, idx) as *const T).as_ref()
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

                if self.flags & (1 << idx) == 0 {
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
                &mut *(<[T; N] as Compound>::get_mut_ptr(&mut self.value, idx) as *mut T)
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
            pub fn get_or_insert_with<F: FnOnce() -> T>(&mut self, idx: usize, f: F) -> &mut T {
                if idx >= N {
                    index_out_of_bounds(idx, N);
                }
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

                if self.is_some(idx as u32) {
                    self.clear_flag(idx as u32);
                    Some(unsafe {
                        (<[T; N] as Compound>::get_ptr(&self.value, idx) as *const T).read()
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
                self.set_flag(idx as u32);
                unsafe {
                    (<[T; N] as Compound>::get_mut_ptr(&mut self.value, idx) as *mut T).write(value);
                }
                result
            }
        }
    }
}

impl_array_methods!(OptionGroup8, Compound8);

/// A group of up to sixteen [`Option`](core::option::Option)s, with the
/// discriminants packed into a single `u16`.
/// 
/// See the [module-level documentation](crate::option_group) for more.
pub struct OptionGroup16<T: Compound16> {
    value: MaybeUninit<T>,
    flags: u16,
}

impl_option_group!(OptionGroup16, Compound16);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple0, 0> get_0, get_mut_0, get_mut_unchecked_0, insert_0, get_or_insert_0, get_or_insert_with_0, take_0, replace_0);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple1, 1> get_1, get_mut_1, get_mut_unchecked_1, insert_1, get_or_insert_1, get_or_insert_with_1, take_1, replace_1);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple2, 2> get_2, get_mut_2, get_mut_unchecked_2, insert_2, get_or_insert_2, get_or_insert_with_2, take_2, replace_2);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple3, 3> get_3, get_mut_3, get_mut_unchecked_3, insert_3, get_or_insert_3, get_or_insert_with_3, take_3, replace_3);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple4, 4> get_4, get_mut_4, get_mut_unchecked_4, insert_4, get_or_insert_4, get_or_insert_with_4, take_4, replace_4);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple5, 5> get_5, get_mut_5, get_mut_unchecked_5, insert_5, get_or_insert_5, get_or_insert_with_5, take_5, replace_5);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple6, 6> get_6, get_mut_6, get_mut_unchecked_6, insert_6, get_or_insert_6, get_or_insert_with_6, take_6, replace_6);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple7, 7> get_7, get_mut_7, get_mut_unchecked_7, insert_7, get_or_insert_7, get_or_insert_with_7, take_7, replace_7);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple8, 8> get_8, get_mut_8, get_mut_unchecked_8, insert_8, get_or_insert_8, get_or_insert_with_8, take_8, replace_8);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple9, 9> get_9, get_mut_9, get_mut_unchecked_9, insert_9, get_or_insert_9, get_or_insert_with_9, take_9, replace_9);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple10, 10> get_10, get_mut_10, get_mut_unchecked_10, insert_10, get_or_insert_10, get_or_insert_with_10, take_10, replace_10);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple11, 11> get_11, get_mut_11, get_mut_unchecked_11, insert_11, get_or_insert_11, get_or_insert_with_11, take_11, replace_11);
impl_array_methods!(OptionGroup16, Compound16);


/// A group of up to 32 [`Option`](core::option::Option)s, with the
/// discriminants packed into a single `u32`.
/// 
/// See the [module-level documentation](crate::option_group) for more.
pub struct OptionGroup32<T: Compound32> {
    value: MaybeUninit<T>,
    flags: u32,
}

impl_option_group!(OptionGroup32, Compound32);
impl_tuple_accessors!(OptionGroup32<Compound32 + Tuple0, 0> get_0, get_mut_0, get_mut_unchecked_0, insert_0, get_or_insert_0, get_or_insert_with_0, take_0, replace_0);
impl_tuple_accessors!(OptionGroup32<Compound32 + Tuple1, 1> get_1, get_mut_1, get_mut_unchecked_1, insert_1, get_or_insert_1, get_or_insert_with_1, take_1, replace_1);
impl_tuple_accessors!(OptionGroup32<Compound32 + Tuple2, 2> get_2, get_mut_2, get_mut_unchecked_2, insert_2, get_or_insert_2, get_or_insert_with_2, take_2, replace_2);
impl_tuple_accessors!(OptionGroup32<Compound32 + Tuple3, 3> get_3, get_mut_3, get_mut_unchecked_3, insert_3, get_or_insert_3, get_or_insert_with_3, take_3, replace_3);
impl_tuple_accessors!(OptionGroup32<Compound32 + Tuple4, 4> get_4, get_mut_4, get_mut_unchecked_4, insert_4, get_or_insert_4, get_or_insert_with_4, take_4, replace_4);
impl_tuple_accessors!(OptionGroup32<Compound32 + Tuple5, 5> get_5, get_mut_5, get_mut_unchecked_5, insert_5, get_or_insert_5, get_or_insert_with_5, take_5, replace_5);
impl_tuple_accessors!(OptionGroup32<Compound32 + Tuple6, 6> get_6, get_mut_6, get_mut_unchecked_6, insert_6, get_or_insert_6, get_or_insert_with_6, take_6, replace_6);
impl_tuple_accessors!(OptionGroup32<Compound32 + Tuple7, 7> get_7, get_mut_7, get_mut_unchecked_7, insert_7, get_or_insert_7, get_or_insert_with_7, take_7, replace_7);
impl_tuple_accessors!(OptionGroup32<Compound32 + Tuple8, 8> get_8, get_mut_8, get_mut_unchecked_8, insert_8, get_or_insert_8, get_or_insert_with_8, take_8, replace_8);
impl_tuple_accessors!(OptionGroup32<Compound32 + Tuple9, 9> get_9, get_mut_9, get_mut_unchecked_9, insert_9, get_or_insert_9, get_or_insert_with_9, take_9, replace_9);
impl_tuple_accessors!(OptionGroup32<Compound32 + Tuple10, 10> get_10, get_mut_10, get_mut_unchecked_10, insert_10, get_or_insert_10, get_or_insert_with_10, take_10, replace_10);
impl_tuple_accessors!(OptionGroup32<Compound32 + Tuple11, 11> get_11, get_mut_11, get_mut_unchecked_11, insert_11, get_or_insert_11, get_or_insert_with_11, take_11, replace_11);
impl_array_methods!(OptionGroup32, Compound32);

/// A group of up to 64 [`Option`](core::option::Option)s, with the
/// discriminants packed into a single `u32`.
/// 
/// See the [module-level documentation](crate::option_group) for more.
pub struct OptionGroup64<T: Compound64> {
    value: MaybeUninit<T>,
    flags: u64,
}

impl_option_group!(OptionGroup64, Compound64);
impl_tuple_accessors!(OptionGroup64<Compound64 + Tuple0, 0> get_0, get_mut_0, get_mut_unchecked_0, insert_0, get_or_insert_0, get_or_insert_with_0, take_0, replace_0);
impl_tuple_accessors!(OptionGroup64<Compound64 + Tuple1, 1> get_1, get_mut_1, get_mut_unchecked_1, insert_1, get_or_insert_1, get_or_insert_with_1, take_1, replace_1);
impl_tuple_accessors!(OptionGroup64<Compound64 + Tuple2, 2> get_2, get_mut_2, get_mut_unchecked_2, insert_2, get_or_insert_2, get_or_insert_with_2, take_2, replace_2);
impl_tuple_accessors!(OptionGroup64<Compound64 + Tuple3, 3> get_3, get_mut_3, get_mut_unchecked_3, insert_3, get_or_insert_3, get_or_insert_with_3, take_3, replace_3);
impl_tuple_accessors!(OptionGroup64<Compound64 + Tuple4, 4> get_4, get_mut_4, get_mut_unchecked_4, insert_4, get_or_insert_4, get_or_insert_with_4, take_4, replace_4);
impl_tuple_accessors!(OptionGroup64<Compound64 + Tuple5, 5> get_5, get_mut_5, get_mut_unchecked_5, insert_5, get_or_insert_5, get_or_insert_with_5, take_5, replace_5);
impl_tuple_accessors!(OptionGroup64<Compound64 + Tuple6, 6> get_6, get_mut_6, get_mut_unchecked_6, insert_6, get_or_insert_6, get_or_insert_with_6, take_6, replace_6);
impl_tuple_accessors!(OptionGroup64<Compound64 + Tuple7, 7> get_7, get_mut_7, get_mut_unchecked_7, insert_7, get_or_insert_7, get_or_insert_with_7, take_7, replace_7);
impl_tuple_accessors!(OptionGroup64<Compound64 + Tuple8, 8> get_8, get_mut_8, get_mut_unchecked_8, insert_8, get_or_insert_8, get_or_insert_with_8, take_8, replace_8);
impl_tuple_accessors!(OptionGroup64<Compound64 + Tuple9, 9> get_9, get_mut_9, get_mut_unchecked_9, insert_9, get_or_insert_9, get_or_insert_with_9, take_9, replace_9);
impl_tuple_accessors!(OptionGroup64<Compound64 + Tuple10, 10> get_10, get_mut_10, get_mut_unchecked_10, insert_10, get_or_insert_10, get_or_insert_with_10, take_10, replace_10);
impl_tuple_accessors!(OptionGroup64<Compound64 + Tuple11, 11> get_11, get_mut_11, get_mut_unchecked_11, insert_11, get_or_insert_11, get_or_insert_with_11, take_11, replace_11);
impl_array_methods!(OptionGroup64, Compound64);

