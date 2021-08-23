# coca - Data Structures with Constant Capacity

[![Crates.io](https://img.shields.io/crates/v/coca.svg)](https://crates.io/crates/coca)
[![Documentation](https://docs.rs/coca/badge.svg)](https://docs.rs/coca)

Allocation-free data structures that make do with the memory they're given.

This makes their temporal performance more consistent, and the memory footprint
dead-simple to predict - but it also means insertions can easily fail, so you'll
need proof you can't break the limit, or a graceful recovery path, which is good
practice in memory-constrained environments anyway.

Currently, four main components are provided:

- `Arena`, a bump-/stack-allocator, plus `Box<'a, T>` the corresponding smart
  pointer,
- `Vec`, a bounded, growable array, generic over not only the element type, but
  also the underlying storage type ([as in this recent proposal][generic-vec])
  and the index type (inspired by [`typed-index-collections`][ticollections]),
- `BinaryHeap`, a priority queue implemented on top of `Vec`,
- `Deque`, a double-ended queue implemented with a ring buffer.

  [generic-vec]: https://internals.rust-lang.org/t/is-custom-allocators-the-right-abstraction/13460
  [ticollections]: https://crates.io/crates/typed-index-collections

This crate is still in early development! Currently on the road map (in no
particular order):

- A [`slotmap`][slotmap]-style pool-allocator, as well as a dense pool optimized
  for iteration speed, as opposed to random access,
- ordered and unordered map and set implementations.

  [slotmap]: https://crates.io/crates/slotmap

## Constructive Feedback and Contributions Welcome!

## Getting Started

To add coca as a dependency, add this to your project's `Cargo.toml`:

```toml
[dependencies]
coca = "0.2"
```

## Optional Features

- `alloc`: By default, coca is `no_std` compatible; this feature flag enables
  some trait implementations for conveniently working with heap-allocated storage.
- `profile`: Enables memory profiling in arenas; see the module-level documentation
  for details.
- `unstable`: If you're working with the nightly rust toolchain, and don't mind
  depending on unstable features, you can enable this feature to get access to
  `InlineObject`, allowing you to create trait objects without indirection.

## License

Licensed under either [Apache License, Version 2.0](LICENSE-APACHE) or
[Zlib license](LICENSE-ZLIB) at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this crate by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.