# 0.3.0 (WIP)
## Breaking Changes

- Rename `ContiguousStorage<T>` to `Storage<R>` and overhaul the interface;
  see [this blog post on the design process][storage-abstraction-v2] for motivation
- Add super traits to `Capacity` trait, add `const MAX_REPRESENTABLE`; implementors
  are no longer required to perform validation on _every_ call
- Remove the `nightly` feature flag and the `feature(min_const_generics)` attribute,
  raising the minimum supported compiler version to 1.51.
- Rename `Array{Vec, Deque, Heap}` to `Inline*` for consistency with `InlineObject`
- Redefine `ArenaStorage` as a struct for compatibility with non-array-like layouts
- Remove `HeapStorage` type alias and add `AllocStorage` struct (similar to `ArenaStorage`)

[storage-abstraction-v2]: https://gist.github.com/teryror/7b9a23fd0cd8dcfbcb6ebd34ee2639f8

## New Features

- `DirectPool`, a direct analogue to `slotmap::SlotMap`
- Experimental `object` module for owned, allocation-free trait objects
- Add support for multiple type declarations in a single `index_type!` invocation
- Implement `Vec::drain_filter` and `Vec::drain_filter_range`
- New `option_group` module for bit-packing discriminants of multiple optional values

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