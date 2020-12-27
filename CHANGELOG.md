# 0.2.0 (WIP)

- Add `BinaryHeap` and `Deque` implementations
- Add `Vec::{into_raw_parts, from_raw_parts}`
- Rename `HeapVec` to `AllocVec` for consistency with `AllocHeap` (chosen in favour of `HeapHeap`)
- Rename `Capacity::into_usize` to `as_usize` to comply with naming conventions
- Fix a bug in `Vec::drain` that made right-open ranges not work correctly
- `HeapVec::with_capacity` takes a value of generic type `I: Capacity` rather than `usize`
- Fix potential undefined behavior in `Vec::{deref, deref_mut, into_iter}` detected by Miri

# 0.1.0 (2020-12-03)

Initial Release