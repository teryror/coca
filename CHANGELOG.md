# 0.2.0 (WIP)

- Fix a bug in `Vec::drain` that made right-open ranges not work correctly
- `HeapVec::with_capacity` takes a value of generic type `I: Capacity` rather than `usize`
- Fix potential undefined behavior in `Vec::{deref, deref_mut, into_iter}` detected by Miri

# 0.1.0 (2020-12-03)

Initial Release