#![cfg(feature = "alloc")]
#![feature(test)]

extern crate std;
extern crate test;

use rand::{rngs::SmallRng, seq::SliceRandom, RngCore, SeedableRng};
use test::Bencher;

trait Map<K, V> {
    fn with_capacity(capacity: usize) -> Self;
    fn get(&self, k: &K) -> Option<&V>;
    fn insert(&mut self, k: K, v: V);
    fn remove(&mut self, k: &K) -> Option<V>;
}

macro_rules! insertions {
    ($fnn:ident, $ty:ty, $n:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = SmallRng::seed_from_u64(0x5432_1012_3454_3210);
            b.iter(|| {
                let mut map = <$ty as Map<u32, u32>>::with_capacity($n);
                for _ in 0..$n {
                    map.insert(rng.next_u32(), rng.next_u32());
                }
            })
        }
    };
}

const LOOKUP_BENCH_N: usize = 500;
macro_rules! lookups {
    ($fnn:ident, $ty:ty, $n:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = SmallRng::seed_from_u64(0x5432_1012_3454_3210);
            let mut map = <$ty as Map<u32, u32>>::with_capacity($n);
            for _ in 0..$n {
                map.insert(rng.next_u32(), rng.next_u32());
            }

            b.iter(|| {
                for _ in 0..LOOKUP_BENCH_N {
                    let k = rng.next_u32();
                    let _ = map.get(&k);
                }
            })
        }
    };
}

macro_rules! removals {
    ($fnn:ident, $ty:ty, $n:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = SmallRng::seed_from_u64(0x5432_1012_3454_3210);
            let mut pairs = coca::AllocVec::with_capacity($n as usize);
            for _ in 0..$n {
                pairs.push((rng.next_u32(), rng.next_u32()));
            }

            b.iter(|| {
                let mut map = <$ty as Map<u32, u32>>::with_capacity($n);
                for &(k, v) in pairs.iter() {
                    map.insert(k, v);
                }

                pairs.shuffle(&mut rng);
                for &(k, v) in pairs.iter() {
                    assert_eq!(map.remove(&k), Some(v));
                }
            });
        }
    };
}

mod unordered {
    use super::*;
    use coca::AllocVec;
    use std::collections::HashMap as StdHashMap;

    #[allow(unconditional_recursion)] // false positive!
    impl<K, V> Map<K, V> for StdHashMap<K, V> {
        fn with_capacity(capacity: usize) -> Self {
            StdHashMap::with_capacity(capacity)
        }

        fn get(&self, k: &K) -> Option<&V> {
            self.get(k)
        }

        fn insert(&mut self, k: K, v: V) {
            self.insert(k, v);
        }

        fn remove(&mut self, k: &K) -> Option<V> {
            self.remove(k)
        }
    }

    insertions!(std_hashmap_16_inserts, StdHashMap<_, _>, 16);
    insertions!(std_hashmap_64_inserts, StdHashMap<_, _>, 64);
    insertions!(std_hashmap_256_inserts, StdHashMap<_, _>, 256);
    insertions!(std_hashmap_1024_inserts, StdHashMap<_, _>, 1024);

    lookups!(std_hashmap_16_lookups, StdHashMap<_, _>, 16);
    lookups!(std_hashmap_64_lookups, StdHashMap<_, _>, 64);
    lookups!(std_hashmap_256_lookups, StdHashMap<_, _>, 256);
    lookups!(std_hashmap_1024_lookups, StdHashMap<_, _>, 1024);

    removals!(std_hashmap_16_removals, StdHashMap<_, _>, 16);
    removals!(std_hashmap_64_removals, StdHashMap<_, _>, 64);
    removals!(std_hashmap_256_removals, StdHashMap<_, _>, 256);
    removals!(std_hashmap_1024_removals, StdHashMap<_, _>, 1024);

    struct VecLinearMap<K, V> {
        keys: AllocVec<K>,
        values: AllocVec<V>,
    }

    impl<K, V> Map<K, V> for VecLinearMap<K, V>
    where
        K: PartialEq + Copy,
        V: Copy,
    {
        fn with_capacity(capacity: usize) -> Self {
            let keys = AllocVec::with_capacity(capacity);
            let values = AllocVec::with_capacity(capacity);
            VecLinearMap { keys, values }
        }

        fn get(&self, k: &K) -> Option<&V> {
            let idx = self.keys.iter().position(|candidate| candidate == k);
            idx.map(|i| &self.values[i])
        }

        fn insert(&mut self, k: K, v: V) {
            self.keys.push(k);
            self.values.push(v);
        }

        fn remove(&mut self, k: &K) -> Option<V> {
            let idx = self.keys.iter().position(|candidate| candidate == k);
            idx.map(|i| {
                self.keys.swap_remove(i);
                self.values.swap_remove(i)
            })
        }
    }

    insertions!(vec_linear_map_16_inserts, VecLinearMap<_, _>, 16);
    insertions!(vec_linear_map_64_inserts, VecLinearMap<_, _>, 64);
    insertions!(vec_linear_map_256_inserts, VecLinearMap<_, _>, 256);
    insertions!(vec_linear_map_1024_inserts, VecLinearMap<_, _>, 1024);

    lookups!(vec_linear_map_16_lookups, VecLinearMap<_, _>, 16);
    lookups!(vec_linear_map_64_lookups, VecLinearMap<_, _>, 64);
    lookups!(vec_linear_map_256_lookups, VecLinearMap<_, _>, 256);
    lookups!(vec_linear_map_1024_lookups, VecLinearMap<_, _>, 1024);

    removals!(vec_linear_map_16_removals, VecLinearMap<_, _>, 16);
    removals!(vec_linear_map_64_removals, VecLinearMap<_, _>, 64);
    removals!(vec_linear_map_256_removals, VecLinearMap<_, _>, 256);
    removals!(vec_linear_map_1024_removals, VecLinearMap<_, _>, 1024);
}

mod ordered {
    use super::*;
    use coca::AllocVec;
    use std::collections::BTreeMap;

    impl<K, V> Map<K, V> for BTreeMap<K, V>
    where
        K: Ord,
    {
        fn with_capacity(_: usize) -> Self {
            BTreeMap::new()
        }

        fn get(&self, k: &K) -> Option<&V> {
            self.get(k)
        }

        fn insert(&mut self, k: K, v: V) {
            self.insert(k, v);
        }

        fn remove(&mut self, k: &K) -> Option<V> {
            self.remove(k)
        }
    }

    insertions!(std_btree_map_16_inserts, BTreeMap<_, _>, 16);
    insertions!(std_btree_map_64_inserts, BTreeMap<_, _>, 64);
    insertions!(std_btree_map_256_inserts, BTreeMap<_, _>, 256);
    insertions!(std_btree_map_1024_inserts, BTreeMap<_, _>, 1024);

    lookups!(std_btree_map_16_lookups, BTreeMap<_, _>, 16);
    lookups!(std_btree_map_64_lookups, BTreeMap<_, _>, 64);
    lookups!(std_btree_map_256_lookups, BTreeMap<_, _>, 256);
    lookups!(std_btree_map_1024_lookups, BTreeMap<_, _>, 1024);

    removals!(std_btree_map_16_removals, BTreeMap<_, _>, 16);
    removals!(std_btree_map_64_removals, BTreeMap<_, _>, 64);
    removals!(std_btree_map_256_removals, BTreeMap<_, _>, 256);
    removals!(std_btree_map_1024_removals, BTreeMap<_, _>, 1024);

    struct OrderedVecMap<K: Ord, V> {
        keys: AllocVec<K>,
        values: AllocVec<V>,
    }

    impl<K: Ord + Copy, V: Copy> Map<K, V> for OrderedVecMap<K, V> {
        fn with_capacity(capacity: usize) -> Self {
            let keys = AllocVec::with_capacity(capacity);
            let values = AllocVec::with_capacity(capacity);

            OrderedVecMap { keys, values }
        }

        fn get(&self, k: &K) -> Option<&V> {
            self.keys.binary_search(k).ok().map(|idx| &self.values[idx])
        }

        fn insert(&mut self, k: K, v: V) {
            match self.keys.binary_search(&k) {
                Ok(idx) => {
                    self.values.replace(idx, v);
                }
                Err(idx) => {
                    self.keys.insert(idx, k);
                    self.values.insert(idx, v);
                }
            }
        }

        fn remove(&mut self, k: &K) -> Option<V> {
            self.keys.binary_search(k).ok().map(|idx| {
                self.keys.remove(idx);
                self.values.remove(idx)
            })
        }
    }

    insertions!(ordered_vec_map_16_inserts, OrderedVecMap<_, _>, 16);
    insertions!(ordered_vec_map_64_inserts, OrderedVecMap<_, _>, 64);
    insertions!(ordered_vec_map_256_inserts, OrderedVecMap<_, _>, 256);
    insertions!(ordered_vec_map_1024_inserts, OrderedVecMap<_, _>, 1024);

    lookups!(ordered_vec_map_16_lookups, OrderedVecMap<_, _>, 16);
    lookups!(ordered_vec_map_64_lookups, OrderedVecMap<_, _>, 64);
    lookups!(ordered_vec_map_256_lookups, OrderedVecMap<_, _>, 256);
    lookups!(ordered_vec_map_1024_lookups, OrderedVecMap<_, _>, 1024);

    removals!(ordered_vec_map_16_removals, OrderedVecMap<_, _>, 16);
    removals!(ordered_vec_map_64_removals, OrderedVecMap<_, _>, 64);
    removals!(ordered_vec_map_256_removals, OrderedVecMap<_, _>, 256);
    removals!(ordered_vec_map_1024_removals, OrderedVecMap<_, _>, 1024);
}
