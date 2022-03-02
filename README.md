# coca - Data Structures with Constant Capacity

[![Crates.io](https://img.shields.io/crates/v/coca.svg)](https://crates.io/crates/coca)
[![Documentation](https://docs.rs/coca/badge.svg)](https://docs.rs/coca)
[![Min. rustc version 1.59.0](https://img.shields.io/badge/Min.%20rustc-v1.59.0-blue)](https://img.shields.io/badge/Min%20rustc-v1.59.0-blue)

Allocation-free data structures that make do with the memory they're given.

```toml
[dependencies]
coca = "0.2"
```

## Overview

Rust's [standard collection library][std-collections] provides efficient
implementations of the most common general purpose programming data structures.
By using the standard implementations, it should be possible for two libraries
to communicate without significant data conversion.

[std-collections]: https://doc.rust-lang.org/std/collections/index.html

However, these standard implementations manage their own memory using an
[Allocator][allocator-trait], defaulting to the global heap. This is generally
convenient, but may pose a problem in some cases, e.g. in (soft) real-time
applications, or in memory-constrained embedded systems, where the
[`alloc`][alloc-crate] crate may not even be available.

[allocator-trait]: https://doc.rust-lang.org/core/alloc/trait.Allocator.html
[alloc-crate]: https://doc.rust-lang.org/alloc/index.html

`coca` aims to serve as a replacement in such environments by providing data
structures that operate on a given block of backing memory, without allocating
on their own. They are generic over the storage type, which may be any of the
following:

- `InlineStorage`: Store the contents inside the `struct`, without indirection.
  Requires capacities that are truly `const`, i.e. statically known at compile time.
- `AllocStorage`: Store the contents in globally allocated memory.
  Requires the `alloc` feature flag.
- `SliceStorage`: For array-like data structures only, store the contents in
  any given slice of uninitialized memory.
- `ArenaStorage`: `coca` includes an [arena allocator][arena-allocator], and
  allows ergonomic construction of data structures using arena-allocated memory
  as storage.

[arena-allocator]: https://en.wikipedia.org/wiki/Region-based_memory_management

Within this paradigm, direct analogs to the following types are provided:

- [`alloc::vec::Vec`](https://doc.rust-lang.org/alloc/vec/struct.Vec.html)
- [`alloc::string::String`](https://doc.rust-lang.org/alloc/string/struct.String.html)
- [`alloc::collections::VecDeque](https://doc.rust-lang.org/alloc/collections/vec_deque/index.html)
- [`alloc::collections::BinaryHeap`](https://doc.rust-lang.org/alloc/collections/binary_heap/struct.BinaryHeap.html)
- [`slotmap::{SlotMap, DenseSlotMap}`](https://docs.rs/slotmap/latest/slotmap/)

Additionally, `coca` also includes the following container types:

- `ListSet`, a set implemented as a `Vec`.
- `ListMap`, an [association list](https://en.wikipedia.org/wiki/Association_list)
  implemented as a pair of parallel arrays.
- `CacheTable`, a forgetful hash map with a configurable eviction policy;
  ideal for caching, hence the name.
- `OptionGroup`, a tuple or array of optional values with the occupancy flags
  packed into a single bitmap field.
- `InlineObject`, a statically-sized container for dynamically-sized types,
  mainly trait objects; this requires unstable language features, and therefore
  needs the `unstable` feature flag to be enabled.

## Comparison with Other Libraries

First of all, unless you are trying to avoid hitting the global allocator, or
don't have one in your target environment, you are almost certainly better off
just using Rust's standard collections, or in the case of `coca::collections::pool`,
the [`slotmap` crate](https://crates.io/crates/slotmap). Even in such a scenario,
however, there are several crates filling a similar niche that are more mature
than `coca`.

### `coca::arena` vs [`bumpalo`](https://crates.io/crates/bumpalo)

- Bumpalo is a `no_std` crate, but it does have a hard dependency on the `alloc`
  crate, which it uses to automatically add chunks to its arenas whenever they
  run out of space. This helps in avoiding failed allocations, but makes it harder
  to bound memory usage. By contrast, `coca`'s dependency on `alloc` is optional;
  a `coca::arena::Arena` always returns `None` (or panics, at your option) when
  it runs out of space, but can be constructed from any mutable byte slice.
- Bumpalo has its own forks of Rust's standard `Vec` and `String` that use its
  `Bump` allocator, and optionally supports the nightly-only `Allocator` API for
  compatibility with the other standard collections. On stable Rust, `coca::arena`
  supports a wider variety of data structures, but it won't benefit from the
  stabilization of `feature(allocator_api)`.
- Uniquely, `coca`'s arenas can be nested, allowing for stack-like de/allocation
  patterns.

### `coca::collections` vs [`heapless`](https://crates.io/crates/heapless)

- `heapless` provides a variety of data structures with statically known
  capacity, the equivalent of `coca`'s `InlineStorage`. It has no support for
  dynamic allocations.
- `heapless` provides direct analogs to `std::collections::HashMap` and
  `HashSet`, which `coca` does not have (yet).
- None of `coca`'s data structures are thread-safe, while `heapless` provides
  multiple synchronization mechanisms: a lock-free memory pool with atomically
  reference-counting pointers, and both MPMC and SPSC lock-free queues.
- `heapless` does not provide equivalents to `std::collections::VecDeque`,
  `slotmap::SlotMap` or `slotmap::DenseSlotMap`, while `coca` does, on top of
  the more niche data structures (`CacheTable`, `OptionGroup`, `InlineObject`).

### `coca::collections::vec` vs [`tinyvec`][1] and [`arrayvec`][2]

[1]: https://crates.io/crates/tinyvec
[2]: https://crates.io/crates/arrayvec

- tinyvec uses no unsafe code, but requires the element type to implement the
  `Default` trait. `coca` has no such restriction, and offers equivalents to
  `tinyvec::ArrayVec` and `tinyvec::SliceVec`, but not `tinyvec::TinyVec`, which
  is a small-size optimized vector with the ability to reallocate. `coca` also
  requires a newer rust version (min. 1.51) than tinyvec (min. 1.34).
- Both arrayvec and tinyvec have optional [`serde`](https://crates.io/crates/serde)
  support, while `coca` does not.
- `coca::collections::Vec` supports more storage modes with just one implementation,
  meaning its instantiations inter-operate more easily, and you can write generic
  code to handle all of them. It is also generic over the index type, similar to
  what is offered by the [`typed_index_collections`][3] crate.

[3]: (https://crates.io/crates/typed-index-collections)

## Feature Flags

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