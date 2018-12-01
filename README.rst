=============
PriorityQueue
============= 
.. image:: https://img.shields.io/crates/v/priority-queue.svg
	   :target: https://crates.io/crates/priority-queue
.. image:: https://travis-ci.org/garro95/priority-queue.svg?branch=master
	   :target: https://travis-ci.org/garro95/priority-queue
	   
This crate implements a Priority Queue with a function to change the priority of an object.
Priority and items are stored in an `OrderMap` and the queue is implemented as a Heap of indexes.


Please read the `API documentation here`__

__ https://docs.rs/priority-queue/

Usage
-----
To use this crate, simply add the following string to your `Cargo.toml`:

	  priority-queue = "0.5.2"

Notice that a change in the last digit (patch number) means that the interface is
backward and forward compatible and contains other type of fixes, like bug fixes or
documentation updates.
A change in the middle digit (minor) means that the interface is backward compatible
but includes something new, so that the previous version may be not forward compatible.
A change in the first, left digit may means a breacking change in the interface, that
will not be backward compatible anymore. Version 1.0.0 may be an exception to this and
may means just that the API is stable and is considered production ready.

Then use the data structure inside your Rust source code as in the following Example.

Remember that, if you need serde support, you should compile using `--features serde`.

Example
-------
.. code:: rust
	  
	  extern crate priority_queue;

	  use priority_queue::PriorityQueue;
	  
	  fn main {
	      let mut pq = PriorityQueue::new();

	      assert!(pq.is_empty());
	      pq.push("Apples", 5);
	      pq.push("Bananas", 8);
	      pq.push("Strawberries", 23);

	      assert_eq!(pq.peek(), &("Strawberries", 23));

	      for (item, _) in pq.into_sorted_iter() {
	          println!("{}", item);
	      }
	  }

	  
Contributing
------------

Feel free to contribute to this project with pull requests and/or issues. All contribution should be under a license compatible with the GNU LGPL.

Changes
-------

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
