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
//! Tuples with 2 to 12 components may be used to define groups of values with mixed types:
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
//! Arrays can be used to define homogeneous groups. A more ergonomic API is provided in this case:
//! 
//! ```
//! # use coca::option_group::OptionGroup8;
//! // todo!();
//! ```

// TODO: get rid of clippy warnings
// TODO: restructure this file, use more macros to cut down on redundant code
// TODO: for the array versions, implement IntoIter and Index
// TODO: Add {Compound32, Compound64} traits, and {OptionGroup32, OptionGroup64} types
// TODO: finish writing documentation
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
            this.as_ptr().wrapping_add(idx) as _
        }
        #[inline(always)]
        fn get_mut_ptr(this: &mut MaybeUninit<Self>, idx: usize) -> *mut () {
            this.as_mut_ptr().wrapping_add(idx) as _
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
#[allow(missing_docs)]
pub trait Compound16: Compound {}

impl<C> Compound16 for C where C: Compound8 {}

impl<A, B, C, D, E, F, G, H, I> Compound16 for (A, B, C, D, E, F, G, H, I) {}
impl<A, B, C, D, E, F, G, H, I, J> Compound16 for (A, B, C, D, E, F, G, H, I, J) {}
impl<A, B, C, D, E, F, G, H, I, J, K> Compound16 for (A, B, C, D, E, F, G, H, I, J, K) {}
impl<A, B, C, D, E, F, G, H, I, J, K, L> Compound16 for (A, B, C, D, E, F, G, H, I, J, K, L) {}

impl_marker_trait_for_arrays!(Compound16 for [9, 10, 11, 12, 13, 14, 15, 16]);

/// A group of up to eight [`Option`](core::option::Option)s, with the
/// discriminants packed into a single `u8`.
/// 
/// See the [module-level documentation](crate::option_group) for more.
pub struct OptionGroup8<T: Compound8> {
    value: MaybeUninit<T>,
    flags: u8,
}

impl<T> OptionGroup8<T>
where
    T: Compound8,
{
    /// Creates a new group with all options set to `None`.
    #[inline(always)]
    pub fn empty() -> Self {
        OptionGroup8 {
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

impl<T> Default for OptionGroup8<T>
where
    T: Compound8,
{
    fn default() -> Self {
        Self::empty()
    }
}

impl<T> Drop for OptionGroup8<T>
where
    T: Compound8,
{
    fn drop(&mut self) {
        unsafe { T::drop_all_in_place(&mut self.value, self.flags as u64); }
    }
}

macro_rules! impl_tuple_accessors {
    ($ogtype:ident < $compoundtrait:ident + $tupletrait:ident , $idx:literal > $get:ident, $get_mut:ident, $take:ident, $replace:ident) => {
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
                    unsafe { (<T as Compound>::get_mut_ptr(&mut self.value, $idx) as *mut <T as $tupletrait>::T).as_mut() }
                }
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

            #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".replace()`](core::option::Option::replace).")]
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

impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple0, 0> get_0, get_mut_0, take_0, replace_0);
impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple1, 1> get_1, get_mut_1, take_1, replace_1);
impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple2, 2> get_2, get_mut_2, take_2, replace_2);
impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple3, 3> get_3, get_mut_3, take_3, replace_3);
impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple4, 4> get_4, get_mut_4, take_4, replace_4);
impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple5, 5> get_5, get_mut_5, take_5, replace_5);
impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple6, 6> get_6, get_mut_6, take_6, replace_6);
impl_tuple_accessors!(OptionGroup8<Compound8 + Tuple7, 7> get_7, get_mut_7, take_7, replace_7);

macro_rules! impl_array_methods {
    ($typename:ident, $traitname:ident) => {
        impl<T, const N: usize> $typename<[T; N]> where [T; N]: $traitname {
            pub fn new(values: [Option<T>; N]) -> Self {
                let mut result = Self::empty();
                for (idx, v) in core::array::IntoIter::new(values).enumerate() {
                    if let Some(value) = v {
                        result.set(idx, value);
                    }
                }

                result
            }

            pub fn get(&self, idx: usize) -> Option<&T> {
                if idx >= N {
                    panic!("Index out of bounds!");
                }

                if self.flags & (1 << idx) == 0 {
                    return None;
                }

                unsafe {
                    (<[T; N] as Compound>::get_ptr(&self.value, idx) as *const T).as_ref()
                }
            }

            pub fn set(&mut self, idx: usize, value: T) {
                if self.is_some(idx as u32) {
                    unsafe {
                        (<[T; N] as Compound>::get_mut_ptr(&mut self.value, idx) as *mut T).drop_in_place();
                        self.set_flag(idx as u32);
                    }
                }

                unsafe {
                    (<[T; N] as Compound>::get_mut_ptr(&mut self.value, idx) as *mut T).write(value);
                }
            }
        }
    }
}

impl_array_methods!(OptionGroup8, Compound8);
impl_array_methods!(OptionGroup16, Compound16);

/// A group of up to sixteen [`Option`](core::option::Option)s, with the
/// discriminants packed into a single `u16`.
/// 
/// See the [module-level documentation](crate::option_group) for more.
pub struct OptionGroup16<T: Compound16> {
    value: MaybeUninit<T>,
    flags: u16,
}

impl<T> OptionGroup16<T>
where
    T: Compound16,
{
    #[inline(always)]
    pub fn empty() -> Self {
        OptionGroup16 {
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

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.flags == 0
    }

    #[inline(always)]
    pub fn is_some(&self, n: u32) -> bool {
        self.flags & (1 << n) != 0
    }

    #[inline(always)]
    pub fn is_none(&self, n: u32) -> bool {
        self.flags & (1 << n) == 0
    }
}

impl<T> Default for OptionGroup16<T>
where
    T: Compound16,
{
    fn default() -> Self {
        Self::empty()
    }
}

impl<T> Drop for OptionGroup16<T>
where
    T: Compound16,
{
    fn drop(&mut self) {
        unsafe { T::drop_all_in_place(&mut self.value, self.flags as u64); }
    }
}

impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple0, 0> get_0, get_mut_0, take_0, replace_0);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple1, 1> get_1, get_mut_1, take_1, replace_1);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple2, 2> get_2, get_mut_2, take_2, replace_2);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple3, 3> get_3, get_mut_3, take_3, replace_3);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple4, 4> get_4, get_mut_4, take_4, replace_4);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple5, 5> get_5, get_mut_5, take_5, replace_5);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple6, 6> get_6, get_mut_6, take_6, replace_6);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple7, 7> get_7, get_mut_7, take_7, replace_7);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple8, 8> get_8, get_mut_8, take_8, replace_8);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple9, 9> get_9, get_mut_9, take_9, replace_9);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple10, 10> get_10, get_mut_10, take_10, replace_10);
impl_tuple_accessors!(OptionGroup16<Compound16 + Tuple11, 11> get_11, get_mut_11, take_11, replace_11);
