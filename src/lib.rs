/*
 *  Copyright 2017 Gianmarco Garrisi and contributors
 *
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Lesser General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version, or (at your opinion) under the terms
 *  of the Mozilla Public License version 2.0.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

//! This crate provides 2 main data structures:
//!  *  a [priority queue](PriorityQueue)
//!  *  a [double priority queue](DoublePriorityQueue).
//!
//! Both data structures are backed by an hashmap, allowing
//! to change the priority of an element with some efficient methods in
//! **O(log(N))** time (worst case).
//!
//! The elements (called `Item`s, of type `I`) must implement
//! [`Hash`](https://doc.rust-lang.org/std/hash/trait.Hash.html)
//! and [`Eq`](https://doc.rust-lang.org/std/cmp/trait.Eq.html) traits.
//!
//! This can frequently be achieved by using `#[derive(PartialEq, Eq, Hash)]`.
//! If you implement these yourself, it is important that the following property holds:
//!
//! ```text
//! k1 == k2 -> hash(k1) == hash(k2)
//! ```
//!
//! In other words, if two keys are equal, their hashes must be equal.
//!
//! The priority `P` may be any type that implements
//! [`Ord`](https://doc.rust-lang.org/std/cmp/trait.Ord.html).
//! For reverse order remember the standard wrapper
//! [`Reverse<T>`](https://doc.rust-lang.org/std/cmp/struct.Reverse.html)
//!
//! # Example
//! ```rust
//! use priority_queue::PriorityQueue;
//!
//! let mut pq = PriorityQueue::new();
//!
//! assert!(pq.is_empty());
//! pq.push("Apples", 5);
//! pq.push("Bananas", 8);
//! pq.push("Strawberries", 23);
//!
//! assert_eq!(pq.peek(), Some((&"Strawberries", &23)));
//!
//! pq.change_priority("Bananas", 25);
//! assert_eq!(pq.peek(), Some((&"Bananas", &25)));
//!
//! for (item, _) in pq.into_sorted_iter() {
//!     println!("{}", item);
//! }
//! ```
#![cfg_attr(not(has_std), no_std)]

#[cfg(not(has_std))]
extern crate alloc;

#[cfg(not(has_std))]
pub(crate) mod std {
    pub use core::*;
    pub mod alloc {
        pub use ::alloc::*;
    }
    pub mod collections {
        pub use ::alloc::collections::*;
    }
    pub use ::alloc::vec;
}

pub mod core_iterators;
pub mod double_priority_queue;
pub mod priority_queue;
mod store;

pub use crate::double_priority_queue::DoublePriorityQueue;
pub use crate::priority_queue::PriorityQueue;

pub(crate) mod heap_common {
    /// The Index of the element in the Map
    #[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
    pub struct Index(pub usize);
    /// The Position of the element in the Heap
    #[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
    pub struct Position(pub usize);

    /// Compute the index of the left child of an item from its index
    #[inline(always)]
    pub const fn left(i: Position) -> Position {
        Position((i.0 * 2) + 1)
    }
    /// Compute the index of the right child of an item from its index
    #[inline(always)]
    pub const fn right(i: Position) -> Position {
        Position((i.0 * 2) + 2)
    }
    /// Compute the index of the parent element in the heap from its index
    #[inline(always)]
    pub const fn parent(i: Position) -> Position {
        Position((i.0 - 1) / 2)
    } // Compute the level of a node from its index

    #[inline(always)]
    pub const fn level(i: Position) -> usize {
        log2_fast(i.0 + 1)
    }

    #[inline(always)]
    pub const fn log2_fast(x: usize) -> usize {
        (8 * usize::BITS - x.leading_zeros() - 1) as usize
    }

    // `rebuild` takes O(len1 + len2) operations
    // and about 2 * (len1 + len2) comparisons in the worst case
    // while `extend` takes O(len2 * log_2(len1)) operations
    // and about 1 * len2 * log_2(len1) comparisons in the worst case,
    // assuming len1 >= len2.
    pub const fn better_to_rebuild(len1: usize, len2: usize) -> bool {
        // log(1) == 0, so the inequation always falsy
        // log(0) is inapplicable and produces panic
        if len1 <= 1 {
            return false;
        }

        2 * (len1 + len2) < len2 * log2_fast(len1)
    }
}
