# 0.3.0 (2022-03-04)
## Breaking Changes

- Rename `ContiguousStorage<T>` to `Storage<R>` and overhaul the interface;
  see [this blog post on the design process][storage-abstraction-v2] for motivation
- Add super traits to `Capacity` trait, add `const MAX_REPRESENTABLE`; implementors
  are no longer required to perform validation on _every_ call
- Remove the `nightly` feature flag and the `feature(min_const_generics)` attribute.
- Rework the module hierarchy, introducing the `collections` module
- Rename `Array{Vec, Deque, Heap}` to `Inline*` for consistency with `InlineObject`;
  remove `TiArrayVec`, `TiArrayDeque`, and `TiArrayHeap` in favor of default type
  parameters on `Inline{Vec, Deque, Heap}`, raising minimum supported compiler version
  to 1.59.0.
- Redefine `ArenaStorage` as a struct for compatibility with non-array-like layouts
- Remove `HeapStorage` type alias and add `AllocStorage` struct (similar to `ArenaStorage`)
- Rename `Arena::{collect, try_collect}` to `Arena::{collect_slice, try_collect_slice}`
- Remove `Arena::{try_vec, try_deque, try_heap, vec, deque, heap}` in favor of
  the generic `Arena::{try_with_capacity, with_capacity}`
- Add the `CapacityError` type, changing the return type of several fallible methods.

[storage-abstraction-v2]: https://gist.github.com/teryror/7b9a23fd0cd8dcfbcb6ebd34ee2639f8

## New Features

- New `string` module for working with UTF-8 encoded text
- New `cache` module for forgetful map data structures
- `DirectPool`, a direct analogue to `slotmap::SlotMap`
- `PackedPool`, a direct analogue to `slotmap::DenseSlotMap`
- New `option_group` module for bit-packing discriminants of multiple optional values
- Experimental `object` module for owned, allocation-free trait objects
- Implement `Vec::drain_filter` and `Vec::drain_filter_range`
- New methods `Deque::force_push_front` and `Deque::force_push_back`
  for using `Deque` as a classic ring buffer
- New methods `Arena::static_with_capacity` for ergonomically constructing arenas when
  the `alloc` crate is available, and `Arena::{collect_with_capacity, try_collect_with_capacity}`,
  which more closely approximate `Iterator::collect` than the old `collect` methods
- Add support for multiple type declarations in a single `index_type!` invocation

## Bugfixes

- Leaking a `vec::Drain` or `deque::Drain` no longer leaves the underlying data structure
  in an invalid state, potentially causing undefined behaviour
- Failing to allocate an array from an `Arena` no longer creates a null reference to an
  empty slice, causing undefined behaviour

# 0.2.0 (2020-12-28)

- Add `BinaryHeap` and `Deque` implementations
- Add `Vec::{into_raw_parts, from_raw_parts}`
- Rename `HeapVec` to `AllocVec` for consistency with `AllocHeap` (chosen in favour of `HeapHeap`)
- Rename `Capacity::into_usize` to `as_usize` and `ArenaWriter` to `Writer` to comply with naming conventions
- Fix a bug in `Vec::drain` that made right-open ranges not work correctly
- `HeapVec::with_capacity` takes a value of generic type `I: Capacity` rather than `usize`
- Fix potential undefined behavior in `Vec::{deref, deref_mut, into_iter}` detected by Miri

# 0.1.0 (2020-12-03)

Initial Release