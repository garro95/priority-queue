/*
 *  Copyright 2017 Gianmarco Garrisi
 *
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Lesser General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
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

use std::cmp::{Ord, Eq};
use std::hash::Hash;

use ordermap::OrderMap;

/// A priority queue with efficient change function to change the priority of an
/// element.
///
/// The priority is of type P, that must implement `std::cmp::Ord`.
/// The item is of typer I, that must implement `Hash` and `Eq`
/// Implemented as an heap of indexes, stores the items inside an `OrderMap`
/// to be able to retrieve them quickly.
#[derive(Clone, Debug)]
pub struct PriorityQueue<I, P>
    where I: Hash+Eq{
    map: OrderMap<I, P>, // Stores the items and assign them an index
    heap: Vec<usize>,    // Implements the heap of indexes
    qp: Vec<usize>,      // Performs the translation from the index
                         // of the map to the index of the heap
    size: usize          // The size of the heap
}

impl<I, P> PriorityQueue<I, P>
    where P: Ord,
          I: Hash + Eq {

    /// Creates an empty `PriorityQueue`
    pub fn new() -> PriorityQueue<I, P> {
        PriorityQueue{
            map: OrderMap::new(),
            heap: Vec::new(),
            qp: Vec::new(),
            size: 0
        }
    }

    /// Creates an empty `PriorityQueue` with the specified capacity.
    ///
    /// The internal collections will be able to hold at least `capacity`
    /// elements without reallocating.
    /// If `capacity` is 0, there will no allocation.
    pub fn with_capacity(capacity: usize) -> PriorityQueue<I, P> {
        PriorityQueue{
            map: OrderMap::with_capacity(capacity),
            heap: Vec::with_capacity(capacity),
            qp: Vec::with_capacity(capacity),
            size: 0
        }
    }

    /// Returns the number of elements the internal map can hold without reallocating.
    ///
    /// This number is a lower bound; the map might be able to hold more,
    /// but is guaranteed to be able to hold at least this many.
    pub fn capacity(&self)->usize {
        self.map.capacity()
    }

    /// Shrinks the capacity of the internal data structures
    /// that support this operation as much as possible.
    pub fn shrink_to_fit(&mut self){
        self.heap.shrink_to_fit();
        self.qp.shrink_to_fit();
    }

    /// Returns the number of elements in the priority queue.
    pub fn len(&self) -> usize {
        self.size
    }

    /// Returns true if the priority queue contains no elements.
    pub fn is_empty(&self) -> bool {
        self.size==0
    }

    /// Insert they item-priority pair into the queue.
    ///
    /// If `item` was already into the queue, the old value of its priority
    /// is returned in `Some`; otherwise, return `None`.
    ///
    /// Computes in **O(log(N))** time.
    pub fn push(&mut self, item: I, priority: P) -> Option<P>{
        // insert the item, priority into the OrderMap
        let r = self.map.insert(item, priority);
        // ... and get a reference to the priority
        let priority = self.map.get_index(self.size).unwrap().1;
        // copy the actual size of the heap
        let mut i = self.size;
        let k = i;
        // add the new element in the qp vector as the last in the heap
        self.qp.push(i);
        self.heap.push(0);
        // from the leaf go up to root or until an element with priority greater
        // than the new element is found
        while (i > 0) &&
            ( self.map.get_index(self.heap[parent(i)]).unwrap().1 < &priority ){
                self.heap[i] = self.heap[parent(i)];
                self.qp[self.heap[i]] = i;
                i = parent(i);
            }
        // put the new element into the heap and update the qp translation table and the size
        self.heap[i] = k;
        self.qp[k] = i;
        self.size += 1;
        r
    }

    /// Returns the couple (item, priority) with the greatest
    /// priority in the queue, or None if it is empty.
    ///
    /// Computes in **O(1)** time
    pub fn peek(&self) -> Option<(&I, &P)>{
        self.map.get_index(self.heap[0])
    }

    /// Returns the couple (item, priority) with the greatest
    /// priority in the queue, or None if it is empty.
    ///
    /// The item is a mutable reference, but it's a logic error to modify it
    /// in a way that change the result of  `Hash` or `Eq`.
    ///
    /// The priority cannot be modified with a call to this function.
    /// To modify the priority use ...
    ///
    /// Computes in **O(1)** time
    pub fn peek_mut(&mut self) -> Option<(&mut I, &P)> {
        self.map.get_index_mut(self.heap[0])
            .map(|pair| (pair.0, &(*pair.1)))
    }

    pub fn pop(&mut self) -> Option<(I, P)> {
        if self.size == 0 {
            return None;
        }
        let result = self.swap_remove();
        if self.size > 0 {
            self.heapify(0);
        }
        result
    }

    /// Remove and return the element with the max priority
    /// and swap it with the last element keeping a consistent
    /// state.
    /// Computes in **O(1)** time (average)
    fn swap_remove(&mut self) -> Option<(I, P)>{
        // swap_remove the head
        let head = self.heap.swap_remove(0);
        self.size -= 1;
        // swap remove the old heap from the qp
        if self.size == 0 {
            self.qp.pop();
            return self.map.swap_remove_index(head);
        }
        self.qp[self.heap[0]] = 0;
        self.qp.swap_remove(head);
        if head < self.size {
            self.heap[self.qp[head]] = head;
        }
        // swap remove from the map and return to the client
        self.map.swap_remove_index(head)
    }

    /// swap two elements keeping a consistent
    /// state.
    /// Computes in **O(1)** time (average)
    fn swap(&mut self, a: usize, b:usize) {
        let (i, j) = (self.heap[a], self.heap[b]);
        self.heap.swap(a, b);
        self.qp.swap(i, j);
    }

    fn heapify(&mut self, i: usize) {
        let (mut l, mut r) = (left(i), right(i));
        let mut i = i;
        let mut largest;
        if l < self.size &&
            self.map.get_index(self.heap[l]).unwrap().1 >
            self.map.get_index(self.heap[i]).unwrap().1
        {
            largest = l;
        } else {
            largest = i;
        }
        if r < self.size &&
            self.map.get_index(self.heap[r]).unwrap().1 >
            self.map.get_index(self.heap[largest]).unwrap().1
        {
            largest = r;
        }
        while largest != i {
            self.swap(i, largest);

            i = largest;
            l = left(i);
            r = right(i);
            if l < self.size &&
                self.map.get_index(self.heap[l]).unwrap().1 >
                self.map.get_index(self.heap[i]).unwrap().1
            {
                largest = l;
            }
            else {
                largest = i;
            }
            if r < self.size &&
                self.map.get_index(self.heap[r]).unwrap().1 >
                self.map.get_index(self.heap[largest]).unwrap().1
            {
                largest = r;
            }
        }
    }
}

#[inline]
fn left(i:usize) -> usize {
    (i*2) +1
}
#[inline]
fn right(i:usize) -> usize {
    (i*2) +2
}
#[inline]
fn parent(i:usize) -> usize{
    (i-1) /2
}
