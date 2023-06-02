# PriorityQueue
[![crate](https://img.shields.io/crates/v/priority-queue.svg)](https://crates.io/crates/priority-queue)
[![Build](https://github.com/garro95/priority-queue/actions/workflows/build.yml/badge.svg)](https://github.com/garro95/priority-queue/actions/workflows/build.yml)
[![Test](https://github.com/garro95/priority-queue/actions/workflows/test.yml/badge.svg)](https://github.com/garro95/priority-queue/actions/workflows/test.yml)

This crate implements a Priority Queue with a function to change the priority of an object.
Priority and items are stored in an `IndexMap` and the queue is implemented as a Heap of indexes.


Please read the [API documentation here](https://docs.rs/priority-queue/)

## Usage

To use this crate, simply add the following string to your `Cargo.toml`:
```
priority-queue = "1.3.0"
```

Version numbers follow the [semver](https://semver.org/) convention.

Then use the data structure inside your Rust source code as in the following Example.

Remember that, if you need serde support, you should compile using `--features serde`.

## Example

```rust
extern crate priority_queue; // not necessary in Rust edition 2018

use priority_queue::PriorityQueue;

fn main() {
    let mut pq = PriorityQueue::new();

    assert!(pq.is_empty());
    pq.push("Apples", 5);
    pq.push("Bananas", 8);
    pq.push("Strawberries", 23);

    assert_eq!(pq.peek(), Some((&"Strawberries", &23)));

    for (item, _) in pq.into_sorted_iter() {
        println!("{}", item);
    }
}
```

Note: in recent versions of Rust (edition 2018) the `extern crate priority_queue` is not necessary anymore!

## Speeding up

You can use custom BuildHasher for the underlying IndexMap and therefore achieve better performance.
For example you can create the queue with the speedy [FxHash](https://github.com/Amanieu/hashbrown) hasher:

```rust
use hashbrown::hash_map::DefaultHashBuilder;

let mut pq = PriorityQueue::<_, _, DefaultHashBuilder>::with_default_hasher();
```

Attention: FxHash does not offer any protection for dos attacks. This means that some pathological inputs can make the operations on the hashmap O(n^2). Use the standard hasher if you cannot control the inputs.

## Benchmarks

Some benchmarks have been run to compare the performances of this priority queue to the standard BinaryHeap, also using the FxHash hasher.
On a Ryzen 9 3900X, the benchmarks produced the following results:
```
test benchmarks::priority_change_on_large_double_queue     ... bench:          25 ns/iter (+/- 1)
test benchmarks::priority_change_on_large_double_queue_fx  ... bench:          21 ns/iter (+/- 1)
test benchmarks::priority_change_on_large_queue            ... bench:          15 ns/iter (+/- 0)
test benchmarks::priority_change_on_large_queue_fx         ... bench:          11 ns/iter (+/- 0)
test benchmarks::priority_change_on_large_queue_std        ... bench:     190,345 ns/iter (+/- 4,976)
test benchmarks::priority_change_on_small_double_queue     ... bench:          26 ns/iter (+/- 0)
test benchmarks::priority_change_on_small_double_queue_fx  ... bench:          20 ns/iter (+/- 0)
test benchmarks::priority_change_on_small_queue            ... bench:          15 ns/iter (+/- 0)
test benchmarks::priority_change_on_small_queue_fx         ... bench:          10 ns/iter (+/- 0)
test benchmarks::priority_change_on_small_queue_std        ... bench:       1,694 ns/iter (+/- 21)
test benchmarks::push_and_pop                              ... bench:          31 ns/iter (+/- 0)
test benchmarks::push_and_pop_double                       ... bench:          31 ns/iter (+/- 0)
test benchmarks::push_and_pop_double_fx                    ... bench:          24 ns/iter (+/- 1)
test benchmarks::push_and_pop_fx                           ... bench:          26 ns/iter (+/- 0)
test benchmarks::push_and_pop_min_on_large_double_queue    ... bench:         101 ns/iter (+/- 2)
test benchmarks::push_and_pop_min_on_large_double_queue_fx ... bench:          98 ns/iter (+/- 0)
test benchmarks::push_and_pop_on_large_double_queue        ... bench:         107 ns/iter (+/- 2)
test benchmarks::push_and_pop_on_large_double_queue_fx     ... bench:         106 ns/iter (+/- 2)
test benchmarks::push_and_pop_on_large_queue               ... bench:          84 ns/iter (+/- 1)
test benchmarks::push_and_pop_on_large_queue_fx            ... bench:          78 ns/iter (+/- 2)
test benchmarks::push_and_pop_on_large_queue_std           ... bench:          71 ns/iter (+/- 1)
test benchmarks::push_and_pop_std                          ... bench:           4 ns/iter (+/- 0)
```

The priority change on the standard queue was obtained with the following:

```rust
pq = pq.drain().map(|Entry(i, p)| {
    if i == 50_000 {
        Entry(i, p/2)
    } else {
        Entry(i, p)
    }
}).collect()
```

The interpretation of the benchmarks is that the data structures provided by this crate is generally slightly slower than the standard Binary Heap.

On small queues (<10000 elements), the change_priority function, obtained on the standard Binary Heap with the code above, is way slower than the one provided by `PriorityQueue` and `DoublePriorityQueue`.
With the queue becoming bigger, the operation takes almost the same amount of time on `PriorityQueue` and `DoublePriorityQueue`, while it takes more and more time for the standard queue.

It also emerges that the ability to arbitrarily pop the minimum or maximum element comes with a cost, that is visible in all the operations on `DoublePriorityQueue`, that are slower then the corresponding operations executed on the `PriorityQueue`.

## Contributing

Feel free to contribute to this project with pull requests and/or issues. All contribution should be under a license compatible with the GNU LGPL and with the MPL.

## Changes

* 1.3.1 Bug fix: [#42](https://github.com/garro95/priority-queue/issues/42)
* 1.3.0 Return bool from `change_priority_by` (Merged [#41](https://github.com/garro95/priority-queue/pull/41))
* 1.2.3 Further performance optimizations (mainly on `DoublePriorityQueue`)
* 1.2.2 Performance optimizations
* 1.2.1 Bug fix: [#34](https://github.com/garro95/priority-queue/issues/34)
* 1.2.0 Implement DoublePriorityQueue data structure
* 1.1.1 Convert documentation to Markdown
* 1.1.0 Smooth `Q: Sized` requirement on some methods (fix [#32](https://github.com/garro95/priority-queue/issues/32))
* 1.0.5 Bug fix: [#28](https://github.com/garro95/priority-queue/issues/28)
* 1.0.4 Bug fix: [#28](https://github.com/garro95/priority-queue/issues/28)
* 1.0.3 Bug fix: [#26](https://github.com/garro95/priority-queue/issues/26)
* 1.0.2 Added documentation link to Cargo.toml so the link is shown in the results page of crates.io
* 1.0.1 Documentation
* 1.0.0 This release contains **breaking changes!**
    * `From` and `FromIterator` now accept custom hashers -- **Breaking:**
      every usage of `from` and `from_iter` must specify some type to help the type inference. To use the default hasher (`RandomState`), often it will be enough to add something like

      ```rust
		let pq: PriorityQueue<_, _> = PriorityQueue::from...
	  ```

      or you can add a type definition like

      ```rust
		type Pq<I, P> = PriorityQueue<I, P>
	  ```

      and then use `Pq::from()` or `Pq::from_iter()`
    * Support no-std architectures
    * Add a method to remove elements at arbitrary positions
    * Remove `take_mut` dependency -- **Breaking:**
      `change_priority_by` signature has changed. Now it takes a priority_setter `F: FnOnce(&mut P)`.
      If you want you can use the unsafe `take_mut` yourself or also use `std::mem::replace`
* 0.7.0 Implement the `push_increase` and `push_decrease` convenience methods.
* 0.6.0 Allow the usage of custom hasher
* 0.5.4 Prevent panic on extending an empty queue
* 0.5.3 New implementation of the `Default` trait avoids the requirement that `P: Default`
* 0.5.2 Fix documentation formatting
* 0.5.1 Add some documentation for `iter_mut()`
* 0.5.0 Fix [#7](https://github.com/garro95/priority-queue/issues/7) implementing the `iter_mut` features
* 0.4.5 Fix [#6](https://github.com/garro95/priority-queue/issues/6) for `change_priority` and `change_priority_by`
* 0.4.4 Fix [#6](https://github.com/garro95/priority-queue/issues/6)
* 0.4.3 Fix [#4](https://github.com/garro95/priority-queue/issues/4) changing the way `PriorityQueue` serializes.
  Note that old serialized `PriorityQueue`s may be incompatible with the new version.
  The API should not be changed instead.
* 0.4.2 Improved performance using some unsafe code in the implementation.
* 0.4.1 Support for `serde` when compiled with `--features serde`.
  `serde` marked as optional and `serde-test` as dev-dipendency.
  Now compiling the crate won't download and compile also `serde-test`, neither `serde` if not needed.
* 0.4.0 Support for serde when compiled with `cfg(serde)`
* 0.3.1 Fix [#3](https://github.com/garro95/priority-queue/issues/3)
* 0.3.0 Implement PartialEq and Eq traits
