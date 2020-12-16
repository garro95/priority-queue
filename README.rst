=============
PriorityQueue
============= 
.. image:: https://img.shields.io/crates/v/priority-queue.svg
	   :target: https://crates.io/crates/priority-queue
.. image:: https://travis-ci.org/garro95/priority-queue.svg?branch=master
	   :target: https://travis-ci.org/garro95/priority-queue
	   
This crate implements a Priority Queue with a function to change the priority of an object.
Priority and items are stored in an `IndexMap` and the queue is implemented as a Heap of indexes.


Please read the `API documentation here`__

__ https://docs.rs/priority-queue/

Usage
-----
To use this crate, simply add the following string to your `Cargo.toml`:

	  priority-queue = "1.0.0"

Version numbers follow the semver__ convention.

__ https://semver.org/

Then use the data structure inside your Rust source code as in the following Example.

Remember that, if you need serde support, you should compile using `--features serde`.

Example
-------
.. code:: rust
	  
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

Note: in recent versions of Rust (edition 2018) the `extern crate priority_queue` is not necessary anymore!

Speeding up
-----------

You can use custom BuildHasher for the underlying IndexMap and therefore achieve better performance.
For example you can create the queue with the speedy FxHash_ hasher:

.. code:: rust

      use hashbrown::hash_map::DefaultHashBuilder;

      let mut pq = PriorityQueue::<_, _, DefaultHashBuilder>::with_default_hasher();

.. _FxHash: https://github.com/Amanieu/hashbrown

Attention: FxHash does not offer any protection for dos attacks. This means that some pathological inputs can make the operations on the hashmap O(n^2). Use the standard hasher if you cannot control the inputs.

Benchmarks
----------
Some benchmarks have been run to compare the performances of this priority queue to the standard BinaryHeap, also using the FxHash hasher.
On a Ryzen 9 3900X, the benchmarks produced the following results:
::
   test benchmarks::priority_change_on_large_queue     ... bench:          20 ns/iter (+/- 0)
   test benchmarks::priority_change_on_large_queue_fx  ... bench:           7 ns/iter (+/- 0)
   test benchmarks::priority_change_on_large_queue_std ... bench:     255,098 ns/iter (+/- 45,542)
   test benchmarks::priority_change_on_small_queue     ... bench:          19 ns/iter (+/- 0)
   test benchmarks::priority_change_on_small_queue_fx  ... bench:           7 ns/iter (+/- 0)
   test benchmarks::priority_change_on_small_queue_std ... bench:       1,741 ns/iter (+/- 24)
   test benchmarks::push_and_pop                       ... bench:          37 ns/iter (+/- 0)
   test benchmarks::push_and_pop_fx                    ... bench:          25 ns/iter (+/- 0)
   test benchmarks::push_and_pop_on_large_queue        ... bench:         185 ns/iter (+/- 3)
   test benchmarks::push_and_pop_on_large_queue_fx     ... bench:         118 ns/iter (+/- 1)
   test benchmarks::push_and_pop_on_large_queue_std    ... bench:          33 ns/iter (+/- 6)
   test benchmarks::push_and_pop_std                   ... bench:           4 ns/iter (+/- 0)

The priority change on the standard queue was obtained with the following:

.. code:: rust

  	    pq = pq.drain().map(|Entry(i, p)| {
		if i == 50_000 {
		    Entry(i, p/2)
		} else {
		    Entry(i, p)
		}
	    }).collect()

The interpretation of the benchmarks is that the data structure provided by this crate is generally slightly slower then the standard Binary Heap.
On small queues (<10000 elements), also the change_priority function, obtained on the standard Binary Heap with the code above, is roughly as fast as the one provided by PriorityQueue.
With the queue becoming bigger though, PriorityQueue performs much faster on priority change operations.


Contributing
------------

Feel free to contribute to this project with pull requests and/or issues. All contribution should be under a license compatible with the GNU LGPL and with the MPL.

Changes
-------

* 1.0.5 Bug fix: `#28 <https://github.com/garro95/priority-queue/issues/28>`_
* 1.0.4 Bug fix: `#28 <https://github.com/garro95/priority-queue/issues/28>`_
* 1.0.3 Bug fix: `#26 <https://github.com/garro95/priority-queue/issues/26>`_
* 1.0.2 Added documentation link to Cargo.toml so the link is shown in the results page of crates.io
* 1.0.1 Documentation
* 1.0.0 This release contains **breaking changes!**
    * ``From`` and ``FromIterator`` now accept custom hashers -- **Breaking:**
      every usage of ``from`` and ``from_iter`` must specify some type to help the type inference. To use the default hasher (``RandomState``), often it will be enough to add something like

      .. code:: rust

		let pq: PriorityQueue<_, _> = PriorityQueue::from...

      or you can add a type definition like

      .. code:: rust

		type Pq<I, P> = PriorityQueue<I, P>

      and then use ``Pq::from()`` or ``Pq::from_iter()``
    * Support no-std architectures
    * Add a method to remove elements at arbitrary positions
    * Remove ``take_mut`` dependency -- **Breaking:**
      ``change_priority_by`` signature has changed. Now it takes a priority_setter ``F: FnOnce(&mut P)``.
      If you want you can use the unsafe ``take_mut`` yourself or also use ``std::mem::replace``
* 0.7.0 Implement the push_increase and push_decrease convenience methods.
* 0.6.0 Allow the usage of custom hasher
* 0.5.4 Prevent panic on extending an empty queue
* 0.5.3 New implementation of the `Default` trait avoids the requirement that `P: Default`
* 0.5.2 Fix documentation formatting
* 0.5.1 Add some documentation for `iter_mut()`
* 0.5.0 Fix #7 implementing the `iter_mut` features
* 0.4.5 Fix #6 for `change_priority` and `change_priority_by`
* 0.4.4 Fix #6
* 0.4.3 Fix #4 changing the way PriorityQueue serializes.
  Note that old serialized PriorityQueues may be incompatible with the new version.
  The API should not be changed instead.
* 0.4.2 Improved performance using some unsafe code in the implementation.
* 0.4.1 Support for serde when compiled with `--features serde`.
  serde marked as optional and serde-test as dev-dipendency.
  Now compiling the crate won't download and compile also serde-test, neither serde if not needed.
* 0.4.0 Support for serde when compiled with `cfg(serde)`
* 0.3.1 Fix #3
* 0.3.0 Implement PartialEq and Eq traits
