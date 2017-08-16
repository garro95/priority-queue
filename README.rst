=============
PriorityQueue
============= 
.. image:: https://img.shields.io/crates/v/priority-queue.svg :target: https://crates.io/crates/priority-queue
.. image:: https://travis-ci.org/garro95/priority-queue.svg?branch=master :target: https://travis-ci.org/garro95/priority-queue
	   
This crate implements a Priority Queue with a function to change the priority of an object.
Priority and items are stored in an `OrderMap` and the queue is implemented as a Heap of indexes.


Please read the `API documentation here`__

__ https://docs.rs/priority-queue/

Example
-------
.. code:: rust
	  
	  extern crate priority-queue;

	  use priority-queue::PriorityQueue;
	  
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
