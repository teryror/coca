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

// TODO: Reconsider how these traits and bounds should work - maybe we can cut down on redundant method implementations?
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

/// Groups of up to eight [`Option`](core::option::Option).
/// Can be packed into an [`OptionGroup8`] or larger.
#[allow(missing_docs)]
pub trait Compound8: Compound {
    type T0;
    type T1;
    type T2;
    type T3;
    type T4;
    type T5;
    type T6;
    type T7;
}

macro_rules! impl_compound_for_tuple {
    ($traitname:ident : $($assoc:ident = $arg:ident),* ; $($empty_assoc:ident),*) => {
        impl<$($arg),*> $traitname for ($($arg),*) {
            $(type $assoc = $arg;)*
            $(type $empty_assoc = ();)*
        }
    };
}

impl_compound_for_tuple!(Compound8 : T0 = A, T1 = B; T2, T3, T4, T5, T6, T7);
impl_compound_for_tuple!(Compound8 : T0 = A, T1 = B, T2 = C; T3, T4, T5, T6, T7);
impl_compound_for_tuple!(Compound8 : T0 = A, T1 = B, T2 = C, T3 = D; T4, T5, T6, T7);
impl_compound_for_tuple!(Compound8 : T0 = A, T1 = B, T2 = C, T3 = D, T4 = E; T5, T6, T7);
impl_compound_for_tuple!(Compound8 : T0 = A, T1 = B, T2 = C, T3 = D, T4 = E, T5 = F; T6, T7);
impl_compound_for_tuple!(Compound8 : T0 = A, T1 = B, T2 = C, T3 = D, T4 = E, T5 = F, T6 = G; T7);
impl_compound_for_tuple!(Compound8 : T0 = A, T1 = B, T2 = C, T3 = D, T4 = E, T5 = F, T6 = G, T7 = H;);

macro_rules! impl_compound_for_array {
    ($traitname:ident [$cap:literal] : $($assoc:ident),* ; $($empty_assoc:ident),*) => {
        impl<T> $traitname for [T; $cap] {
            $(type $assoc = T;)*
            $(type $empty_assoc = ();)*
        }
    }
}

impl_compound_for_array!(Compound8 [2] : T0, T1; T2, T3, T4, T5, T6, T7);
impl_compound_for_array!(Compound8 [3] : T0, T1, T2; T3, T4, T5, T6, T7);
impl_compound_for_array!(Compound8 [4] : T0, T1, T2, T3; T4, T5, T6, T7);
impl_compound_for_array!(Compound8 [5] : T0, T1, T2, T3, T4; T5, T6, T7);
impl_compound_for_array!(Compound8 [6] : T0, T1, T2, T3, T4, T5; T6, T7);
impl_compound_for_array!(Compound8 [7] : T0, T1, T2, T3, T4, T5, T6; T7);
impl_compound_for_array!(Compound8 [8] : T0, T1, T2, T3, T4, T5, T6, T7;);

/// Groups of up to sixteen [`Option`](core::option::Option).
/// Can be packed into an [`OptionGroup16`] or larger.
#[allow(missing_docs)]
pub trait Compound16: Compound {
    type T0;
    type T1;
    type T2;
    type T3;
    type T4;
    type T5;
    type T6;
    type T7;
    type T8;
    type T9;
    type TA;
    type TB;
    type TC;
    type TD;
    type TE;
    type TF;
}

impl<C> Compound16 for C
where
    C: Compound8,
{
    type T0 = C::T0;
    type T1 = C::T1;
    type T2 = C::T2;
    type T3 = C::T3;
    type T4 = C::T4;
    type T5 = C::T5;
    type T6 = C::T6;
    type T7 = C::T7;
    type T8 = ();
    type T9 = ();
    type TA = ();
    type TB = ();
    type TC = ();
    type TD = ();
    type TE = ();
    type TF = ();
}

impl_compound_for_tuple!(Compound16 : T0 = A, T1 = B, T2 = C, T3 = D, T4 = E, T5 = F, T6 = G, T7 = H, T8 = I; T9, TA, TB, TC, TD, TE, TF);
impl_compound_for_tuple!(Compound16 : T0 = A, T1 = B, T2 = C, T3 = D, T4 = E, T5 = F, T6 = G, T7 = H, T8 = I, T9 = J; TA, TB, TC, TD, TE, TF);
impl_compound_for_tuple!(Compound16 : T0 = A, T1 = B, T2 = C, T3 = D, T4 = E, T5 = F, T6 = G, T7 = H, T8 = I, T9 = J, TA = K; TB, TC, TD, TE, TF);
impl_compound_for_tuple!(Compound16 : T0 = A, T1 = B, T2 = C, T3 = D, T4 = E, T5 = F, T6 = G, T7 = H, T8 = I, T9 = J, TA = K, TB = L; TC, TD, TE, TF);

impl_compound_for_array!(Compound16 [9] : T0, T1, T2, T3, T4, T5, T6, T7, T8; T9, TA, TB, TC, TD, TE, TF);
impl_compound_for_array!(Compound16 [10] : T0, T1, T2, T3, T4, T5, T6, T7, T8, T9; TA, TB, TC, TD, TE, TF);
impl_compound_for_array!(Compound16 [11] : T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA; TB, TC, TD, TE, TF);
impl_compound_for_array!(Compound16 [12] : T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB; TC, TD, TE, TF);
impl_compound_for_array!(Compound16 [13] : T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB, TC; TD, TE, TF);
impl_compound_for_array!(Compound16 [14] : T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB, TC, TD; TE, TF);
impl_compound_for_array!(Compound16 [15] : T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB, TC, TD, TE; TF);
impl_compound_for_array!(Compound16 [16] : T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB, TC, TD, TE, TF;);

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

macro_rules! impl_field_access_methods {
    ($generic:ty, $idx:literal, $t:ty, $get:ident, $get_mut:ident, $take:ident, $replace:ident) => {
        #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".as_ref()`](core::option::Option::as_ref).")]
        #[inline(always)]
        pub fn $get(&self) -> Option<&$t> {
            if self.is_none($idx) {
                None
            } else {
                unsafe { (<$generic as Compound>::get_ptr(&self.value, $idx) as *const $t).as_ref() }
            }
        }

        #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".as_mut()`](core::option::Option::as_mut).")]
        #[inline(always)]
        pub fn $get_mut(&mut self) -> Option<&mut $t> {
            if self.is_none($idx) {
                None
            } else {
                unsafe { (<$generic as Compound>::get_mut_ptr(&mut self.value, $idx) as *mut $t).as_mut() }
            }
        }

        #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".take()`](core::option::Option::take).")]
        #[inline(always)]
        pub fn $take(&mut self) -> Option<$t> {
            if self.is_none($idx) {
                None
            } else {
                self.clear_flag($idx);
                unsafe { Some((<$generic as Compound>::get_ptr(&self.value, $idx) as *const $t).read()) }
            }
        }

        #[doc = concat!(" Equivalent to [`tuple_of_options.", $idx, ".replace()`](core::option::Option::replace).")]
        #[inline(always)]
        pub fn $replace(&mut self, value: $t) -> Option<$t> {
            let result = self.$take();
            unsafe { (<$generic as Compound>::get_mut_ptr(&mut self.value, $idx) as *mut $t).write(value) };
            self.set_flag($idx);
            result
        }
    };
}

impl<T0, T1> OptionGroup8<(T0, T1)> {
    impl_field_access_methods!((T0, T1), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1), 1, T1, get_1, get_mut_1, take_1, replace_1);
}

impl<T0, T1, T2> OptionGroup8<(T0, T1, T2)> {
    impl_field_access_methods!((T0, T1, T2), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2), 2, T2, get_2, get_mut_2, take_2, replace_2);
}

impl<T0, T1, T2, T3> OptionGroup8<(T0, T1, T2, T3)> {
    impl_field_access_methods!((T0, T1, T2, T3), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2, T3), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2, T3), 2, T2, get_2, get_mut_2, take_2, replace_2);
    impl_field_access_methods!((T0, T1, T2, T3), 3, T3, get_3, get_mut_3, take_3, replace_3);
}

impl<T0, T1, T2, T3, T4> OptionGroup8<(T0, T1, T2, T3, T4)> {
    impl_field_access_methods!((T0, T1, T2, T3, T4), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2, T3, T4), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2, T3, T4), 2, T2, get_2, get_mut_2, take_2, replace_2);
    impl_field_access_methods!((T0, T1, T2, T3, T4), 3, T3, get_3, get_mut_3, take_3, replace_3);
    impl_field_access_methods!((T0, T1, T2, T3, T4), 4, T4, get_4, get_mut_4, take_4, replace_4);
}

impl<T0, T1, T2, T3, T4, T5> OptionGroup8<(T0, T1, T2, T3, T4, T5)> {
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5), 2, T2, get_2, get_mut_2, take_2, replace_2);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5), 3, T3, get_3, get_mut_3, take_3, replace_3);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5), 4, T4, get_4, get_mut_4, take_4, replace_4);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5), 5, T5, get_5, get_mut_5, take_5, replace_5);
}

impl<T0, T1, T2, T3, T4, T5, T6> OptionGroup8<(T0, T1, T2, T3, T4, T5, T6)> {
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6), 2, T2, get_2, get_mut_2, take_2, replace_2);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6), 3, T3, get_3, get_mut_3, take_3, replace_3);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6), 4, T4, get_4, get_mut_4, take_4, replace_4);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6), 5, T5, get_5, get_mut_5, take_5, replace_5);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6), 6, T6, get_6, get_mut_6, take_6, replace_6);
}

impl<T0, T1, T2, T3, T4, T5, T6, T7> OptionGroup8<(T0, T1, T2, T3, T4, T5, T6, T7)> {
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 2, T2, get_2, get_mut_2, take_2, replace_2);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 3, T3, get_3, get_mut_3, take_3, replace_3);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 4, T4, get_4, get_mut_4, take_4, replace_4);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 5, T5, get_5, get_mut_5, take_5, replace_5);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 6, T6, get_6, get_mut_6, take_6, replace_6);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 7, T7, get_7, get_mut_7, take_7, replace_7);
}

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

impl<T0, T1> OptionGroup16<(T0, T1)> {
    impl_field_access_methods!((T0, T1), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1), 1, T1, get_1, get_mut_1, take_1, replace_1);
}

impl<T0, T1, T2> OptionGroup16<(T0, T1, T2)> {
    impl_field_access_methods!((T0, T1, T2), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2), 2, T2, get_2, get_mut_2, take_2, replace_2);
}

impl<T0, T1, T2, T3> OptionGroup16<(T0, T1, T2, T3)> {
    impl_field_access_methods!((T0, T1, T2, T3), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2, T3), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2, T3), 2, T2, get_2, get_mut_2, take_2, replace_2);
    impl_field_access_methods!((T0, T1, T2, T3), 3, T3, get_3, get_mut_3, take_3, replace_3);
}

impl<T0, T1, T2, T3, T4> OptionGroup16<(T0, T1, T2, T3, T4)> {
    impl_field_access_methods!((T0, T1, T2, T3, T4), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2, T3, T4), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2, T3, T4), 2, T2, get_2, get_mut_2, take_2, replace_2);
    impl_field_access_methods!((T0, T1, T2, T3, T4), 3, T3, get_3, get_mut_3, take_3, replace_3);
    impl_field_access_methods!((T0, T1, T2, T3, T4), 4, T4, get_4, get_mut_4, take_4, replace_4);
}

impl<T0, T1, T2, T3, T4, T5> OptionGroup16<(T0, T1, T2, T3, T4, T5)> {
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5), 2, T2, get_2, get_mut_2, take_2, replace_2);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5), 3, T3, get_3, get_mut_3, take_3, replace_3);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5), 4, T4, get_4, get_mut_4, take_4, replace_4);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5), 5, T5, get_5, get_mut_5, take_5, replace_5);
}

impl<T0, T1, T2, T3, T4, T5, T6> OptionGroup16<(T0, T1, T2, T3, T4, T5, T6)> {
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6), 2, T2, get_2, get_mut_2, take_2, replace_2);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6), 3, T3, get_3, get_mut_3, take_3, replace_3);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6), 4, T4, get_4, get_mut_4, take_4, replace_4);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6), 5, T5, get_5, get_mut_5, take_5, replace_5);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6), 6, T6, get_6, get_mut_6, take_6, replace_6);
}

impl<T0, T1, T2, T3, T4, T5, T6, T7> OptionGroup16<(T0, T1, T2, T3, T4, T5, T6, T7)> {
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 2, T2, get_2, get_mut_2, take_2, replace_2);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 3, T3, get_3, get_mut_3, take_3, replace_3);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 4, T4, get_4, get_mut_4, take_4, replace_4);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 5, T5, get_5, get_mut_5, take_5, replace_5);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 6, T6, get_6, get_mut_6, take_6, replace_6);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7), 7, T7, get_7, get_mut_7, take_7, replace_7);
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8> OptionGroup16<(T0, T1, T2, T3, T4, T5, T6, T7, T8)> {
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8), 2, T2, get_2, get_mut_2, take_2, replace_2);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8), 3, T3, get_3, get_mut_3, take_3, replace_3);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8), 4, T4, get_4, get_mut_4, take_4, replace_4);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8), 5, T5, get_5, get_mut_5, take_5, replace_5);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8), 6, T6, get_6, get_mut_6, take_6, replace_6);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8), 7, T7, get_7, get_mut_7, take_7, replace_7);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8), 8, T8, get_8, get_mut_8, take_8, replace_8);
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> OptionGroup16<(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)> {
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9), 2, T2, get_2, get_mut_2, take_2, replace_2);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9), 3, T3, get_3, get_mut_3, take_3, replace_3);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9), 4, T4, get_4, get_mut_4, take_4, replace_4);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9), 5, T5, get_5, get_mut_5, take_5, replace_5);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9), 6, T6, get_6, get_mut_6, take_6, replace_6);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9), 7, T7, get_7, get_mut_7, take_7, replace_7);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9), 8, T8, get_8, get_mut_8, take_8, replace_8);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9), 9, T9, get_9, get_mut_9, take_9, replace_9);
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA>
    OptionGroup16<(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA)>
{
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA), 2, T2, get_2, get_mut_2, take_2, replace_2);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA), 3, T3, get_3, get_mut_3, take_3, replace_3);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA), 4, T4, get_4, get_mut_4, take_4, replace_4);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA), 5, T5, get_5, get_mut_5, take_5, replace_5);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA), 6, T6, get_6, get_mut_6, take_6, replace_6);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA), 7, T7, get_7, get_mut_7, take_7, replace_7);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA), 8, T8, get_8, get_mut_8, take_8, replace_8);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA), 9, T9, get_9, get_mut_9, take_9, replace_9);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA), 10, TA, get_10, get_mut_10, take_10, replace_10);
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB>
    OptionGroup16<(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB)>
{
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB), 0, T0, get_0, get_mut_0, take_0, replace_0);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB), 1, T1, get_1, get_mut_1, take_1, replace_1);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB), 2, T2, get_2, get_mut_2, take_2, replace_2);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB), 3, T3, get_3, get_mut_3, take_3, replace_3);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB), 4, T4, get_4, get_mut_4, take_4, replace_4);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB), 5, T5, get_5, get_mut_5, take_5, replace_5);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB), 6, T6, get_6, get_mut_6, take_6, replace_6);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB), 7, T7, get_7, get_mut_7, take_7, replace_7);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB), 8, T8, get_8, get_mut_8, take_8, replace_8);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB), 9, T9, get_9, get_mut_9, take_9, replace_9);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB), 10, TA, get_10, get_mut_10, take_10, replace_10);
    impl_field_access_methods!((T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, TA, TB), 11, TB, get_11, get_mut_11, take_11, replace_11);
}
