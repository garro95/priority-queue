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

// an improvement in terms of complexity would be to use a bare HashMap
// as vec instead of the IndexMap
use crate::iterators::*;

use std::borrow::Borrow;
use std::cmp::{Eq, Ord};
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash};
use std::iter::Iterator;
use std::mem::{replace, swap};

use indexmap::map::{IndexMap, MutableKeys};
use take_mut::take;

/// A priority queue with efficient change function to change the priority of an
/// element.
///
/// The priority is of type P, that must implement `std::cmp::Ord`.
///
/// The item is of type I, that must implement `Hash` and `Eq`.
///
/// Implemented as a heap of indexes, stores the items inside an `IndexMap`
/// to be able to retrieve them quickly.
#[derive(Clone)]
pub struct PriorityQueue<I, P, H = RandomState>
where
    I: Hash + Eq,
    P: Ord,
{
    pub(crate) map: IndexMap<I, P, H>, // Stores the items and assign them an index
    heap: Vec<usize>,                  // Implements the heap of indexes
    qp: Vec<usize>,                    // Performs the translation from the index
    // of the map to the index of the heap
    size: usize, // The size of the heap
}

// do not [derive(Eq)] to loosen up trait requirements for other types and impls
impl<I, P, H> Eq for PriorityQueue<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher,
{
}

impl<I, P, H> Default for PriorityQueue<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher + Default,
{
    fn default() -> Self {
        Self::with_default_hasher()
    }
}

impl<I, P> PriorityQueue<I, P>
where
    P: Ord,
    I: Hash + Eq,
{
    /// Creates an empty `PriorityQueue`
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Creates an empty `PriorityQueue` with the specified capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_default_hasher(capacity)
    }
}

impl<I, P, H> PriorityQueue<I, P, H>
where
    P: Ord,
    I: Hash + Eq,
    H: BuildHasher + Default,
{
    /// Creates an empty `PriorityQueue` with the default hasher
    pub fn with_default_hasher() -> Self {
        Self::with_capacity_and_default_hasher(0)
    }

    /// Creates an empty `PriorityQueue` with the specified capacity and default hasher
    pub fn with_capacity_and_default_hasher(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, H::default())
    }
}

impl<I, P, H> PriorityQueue<I, P, H>
where
    P: Ord,
    I: Hash + Eq,
    H: BuildHasher,
{
    /// Creates an empty `PriorityQueue` with the specified hasher
    pub fn with_hasher(hash_builder: H) -> Self {
        Self::with_capacity_and_hasher(0, hash_builder)
    }

    /// Creates an empty `PriorityQueue` with the specified capacity and hasher
    ///
    /// The internal collections will be able to hold at least `capacity`
    /// elements without reallocating.
    /// If `capacity` is 0, there will be no allocation.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: H) -> Self {
        Self {
            map: IndexMap::with_capacity_and_hasher(capacity, hash_builder),
            heap: Vec::with_capacity(capacity),
            qp: Vec::with_capacity(capacity),
            size: 0,
        }
    }

    /// Returns an iterator in arbitrary order over the
    /// (item, priority) elements in the queue
    pub fn iter(&self) -> crate::pqueue::Iter<I, P> {
        crate::pqueue::Iter {
            iter: self.map.iter(),
        }
    }
}

impl<I, P, H> PriorityQueue<I, P, H>
where
    P: Ord,
    I: Hash + Eq,
{
    /// Return an iterator in arbitrary order over the
    /// (item, priority) elements in the queue.
    ///
    /// The item and the priority are mutable references, but it's a logic error
    /// to modify the item in a way that change the result of `Hash` or `Eq`.
    ///
    /// It's *not* an error, instead, to modify the priorities, because the heap
    /// will be rebuilt once the `IterMut` goes out of scope. It would be
    /// rebuilt even if no priority value would have been modified, but the
    /// procedure will not move anything, but just compare the priorities.
    pub fn iter_mut(&mut self) -> crate::pqueue::IterMut<I, P, H> {
        crate::pqueue::IterMut::new(self)
    }

    /// Returns the couple (item, priority) with the greatest
    /// priority in the queue, or None if it is empty.
    ///
    /// Computes in **O(1)** time
    pub fn peek(&self) -> Option<(&I, &P)> {
        if self.size == 0 {
            return None;
        }
        self.map.get_index(unsafe { *self.heap.get_unchecked(0) })
    }

    /// Returns the couple (item, priority) with the greatest
    /// priority in the queue, or None if it is empty.
    ///
    /// The item is a mutable reference, but it's a logic error to modify it
    /// in a way that change the result of  `Hash` or `Eq`.
    ///
    /// The priority cannot be modified with a call to this function.
    /// To modify the priority use `push`, `change_priority` or
    /// `change_priority_by`.
    ///
    /// Computes in **O(1)** time
    pub fn peek_mut(&mut self) -> Option<(&mut I, &P)> {
        if self.size == 0 {
            return None;
        }
        self.map
            .get_index_mut(unsafe { *self.heap.get_unchecked(0) })
            .map(|(k, v)| (k, &*v))
    }

    /// Returns the number of elements the internal map can hold without
    /// reallocating.
    ///
    /// This number is a lower bound; the map might be able to hold more,
    /// but is guaranteed to be able to hold at least this many.
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }
}
impl<I, P, H> PriorityQueue<I, P, H>
where
    P: Ord,
    I: Hash + Eq,
    H: BuildHasher,
{
    // reserve_exact -> IndexMap does not implement reserve_exact

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `PriorityQueue`. The collection may reserve more space to avoid
    /// frequent reallocations. After calling `reserve`, capacity will be
    /// greater than or equal to `self.len() + additional`. Does nothing if
    /// capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    pub fn reserve(&mut self, additional: usize) {
        self.map.reserve(additional);
        self.heap.reserve(additional);
        self.qp.reserve(additional);
    }
}

impl<I, P, H> PriorityQueue<I, P, H>
where
    P: Ord,
    I: Hash + Eq,
{
    /// Shrinks the capacity of the internal data structures
    /// that support this operation as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.heap.shrink_to_fit();
        self.qp.shrink_to_fit();
    }

    /// Removes the item with the greatest priority from
    /// the priority queue and returns the pair (item, priority),
    /// or None if the queue is empty.
    pub fn pop(&mut self) -> Option<(I, P)> {
        match self.size {
            0 => None,
            1 => self.swap_remove(),
            _ => {
                let r = self.swap_remove();
                self.heapify(0);
                r
            }
        }
    }
}

impl<I, P, H> PriorityQueue<I, P, H>
where
    P: Ord,
    I: Hash + Eq,
    H: BuildHasher,
{
    /// Insert the item-priority pair into the queue.
    ///
    /// If an element equal to `item` was already into the queue,
    /// it is updated and the old value of its priority returned in `Some`;
    /// otherwise, return `None`.
    ///
    /// Computes in **O(log(N))** time.
    pub fn push(&mut self, item: I, priority: P) -> Option<P> {
        use indexmap::map::Entry::*;
        let mut pos = 0;
        let mut oldp = None;

        match self.map.entry(item) {
            Occupied(mut e) => {
                oldp = Some(replace(e.get_mut(), priority));
                pos = unsafe { *self.qp.get_unchecked(e.index()) };
            }
            Vacant(e) => {
                e.insert(priority);
            }
        }

        if oldp.is_some() {
            unsafe {
                let tmp = *self.heap.get_unchecked(pos);
                while (pos > 0)
                    && (self
                        .map
                        .get_index(*self.heap.get_unchecked(parent(pos)))
                        .unwrap()
                        .1
                        < self.map.get_index(tmp).unwrap().1)
                {
                    *self.heap.get_unchecked_mut(pos) = *self.heap.get_unchecked(parent(pos));
                    *self.qp.get_unchecked_mut(*self.heap.get_unchecked(pos)) = pos;
                    pos = parent(pos);
                }
                *self.heap.get_unchecked_mut(pos) = tmp;
                *self.qp.get_unchecked_mut(tmp) = pos;
            }
            self.heapify(pos);
            return oldp;
        }
        // get a reference to the priority
        let priority = self.map.get_index(self.size).unwrap().1;
        // copy the actual size of the heap
        let mut i = self.size;
        let k = i;
        // add the new element in the qp vector as the last in the heap
        self.qp.push(i);
        self.heap.push(0);
        // from the leaf go up to root or until an element with priority greater
        // than the new element is found
        unsafe {
            while (i > 0)
                && (self
                    .map
                    .get_index(*self.heap.get_unchecked(parent(i)))
                    .unwrap()
                    .1
                    < priority)
            {
                *self.heap.get_unchecked_mut(i) = *self.heap.get_unchecked(parent(i));
                *self.qp.get_unchecked_mut(*self.heap.get_unchecked(i)) = i;
                i = parent(i);
            }
            // put the new element into the heap and
            // update the qp translation table and the size
            *self.heap.get_unchecked_mut(i) = k;
            *self.qp.get_unchecked_mut(k) = i;
        }
        self.size += 1;
        None
    }

    /// Increase the priority of an existing item in the queue, or
    /// insert it if not present.
    ///
    /// If an element equal to `item` is already in the queue with a
    /// lower priority, its priority is increased to the new one
    /// without replacing the element and the old priority is returned.
    /// Otherwise, the new element is inserted into the queue.
    ///
    /// Returns `Some` if an element equal to `item` is already in the
    /// queue. If its priority is higher then `priority`, the latter is returned back,
    /// otherwise, the old priority is contained in the Option.
    /// If the item is not in the queue, `None` is returned.
    ///
    /// Computes in **O(log(N))** time.
    pub fn push_increase(&mut self, item: I, priority: P) -> Option<P> {
        if self.get_priority(&item).map_or(true, |p| priority > *p) {
            self.push(item, priority)
        } else {
            Some(priority)
        }
    }

    /// Decrease the priority of an existing item in the queue, or
    /// insert it if not present.
    ///
    /// If an element equal to `item` is already in the queue with a
    /// higher priority, its priority is decreased to the new one
    /// without replacing the element and the old priority is returned.
    /// Otherwise, the new element is inserted into the queue.
    ///
    /// Returns `Some` if an element equal to `item` is already in the
    /// queue. If its priority is lower then `priority`, the latter is returned back,
    /// otherwise, the old priority is contained in the Option.
    /// If the item is not in the queue, `None` is returned.
    ///
    /// Computes in **O(log(N))** time.
    pub fn push_decrease(&mut self, item: I, priority: P) -> Option<P> {
        if self.get_priority(&item).map_or(true, |p| priority < *p) {
            self.push(item, priority)
        } else {
            Some(priority)
        }
    }

    /// Change the priority of an Item returning the old value of priority,
    /// or `None` if the item wasn't in the queue.
    ///
    /// The argument `item` is only used for lookup, and is not used to overwrite the item's data
    /// in the priority queue.
    ///
    /// The item is found in **O(1)** thanks to the hash table.
    /// The operation is performed in **O(log(N))** time.
    pub fn change_priority<Q: ?Sized>(&mut self, item: &Q, mut new_priority: P) -> Option<P>
    where
        I: Borrow<Q>,
        Q: Eq + Hash,
    {
        let mut pos;
        let r = if let Some((index, _, p)) = self.map.get_full_mut(item) {
            swap(p, &mut new_priority);
            pos = unsafe { *self.qp.get_unchecked(index) };
            Some(new_priority)
        } else {
            return None;
        };
        if r.is_some() {
            unsafe {
                let tmp = *self.heap.get_unchecked(pos);
                while (pos > 0)
                    && (self
                        .map
                        .get_index(*self.heap.get_unchecked(parent(pos)))
                        .unwrap()
                        .1
                        < self.map.get_index(tmp).unwrap().1)
                {
                    *self.heap.get_unchecked_mut(pos) = *self.heap.get_unchecked(parent(pos));
                    *self.qp.get_unchecked_mut(*self.heap.get_unchecked(pos)) = pos;
                    pos = parent(pos);
                }
                *self.heap.get_unchecked_mut(pos) = tmp;
                *self.qp.get_unchecked_mut(tmp) = pos;
            }
            self.heapify(pos);
        }
        r
    }

    /// Change the priority of an Item using the provided function.
    /// The item is found in **O(1)** thanks to the hash table.
    /// The operation is performed in **O(log(N))** time (worst case).
    pub fn change_priority_by<Q: ?Sized, F>(&mut self, item: &Q, priority_setter: F)
    where
        I: Borrow<Q>,
        Q: Eq + Hash,
        F: FnOnce(P) -> P,
    {
        let mut pos = 0;
        let mut found = false;
        if let Some((index, _, p)) = self.map.get_full_mut(item) {
            take(p, priority_setter);
            pos = unsafe { *self.qp.get_unchecked(index) };
            found = true;
        }
        if found {
            unsafe {
                let tmp = *self.heap.get_unchecked(pos);
                while (pos > 0)
                    && (self
                        .map
                        .get_index(*self.heap.get_unchecked(parent(pos)))
                        .unwrap()
                        .1
                        < self.map.get_index(tmp).unwrap().1)
                {
                    *self.heap.get_unchecked_mut(pos) = *self.heap.get_unchecked(parent(pos));
                    *self.qp.get_unchecked_mut(*self.heap.get_unchecked(pos)) = pos;
                    pos = parent(pos);
                }
                *self.heap.get_unchecked_mut(pos) = tmp;
                *self.qp.get_unchecked_mut(tmp) = pos;
            }
            self.heapify(pos);
        }
    }

    /// Get the priority of an item, or `None`, if the item is not in the queue
    pub fn get_priority<Q: ?Sized>(&self, item: &Q) -> Option<&P>
    where
        I: Borrow<Q>,
        Q: Eq + Hash,
    {
        self.map.get(item)
    }

    /// Get the couple (item, priority) of an arbitrary element, as reference
    /// or `None` if the item is not in the queue.
    pub fn get<Q>(&self, item: &Q) -> Option<(&I, &P)>
    where
        I: Borrow<Q>,
        Q: Eq + Hash,
    {
        self.map.get_full(item).map(|(_, k, v)| (k, v))
    }

    /// Get the couple (item, priority) of an arbitrary element, or `None`
    /// if the item was not in the queue.
    ///
    /// The item is a mutable reference, but it's a logic error to modify it
    /// in a way that change the result of  `Hash` or `Eq`.
    ///
    /// The priority cannot be modified with a call to this function.
    /// To modify the priority use `push`, `change_priority` or
    /// `change_priority_by`.
    pub fn get_mut<Q>(&mut self, item: &Q) -> Option<(&mut I, &P)>
    where
        I: Borrow<Q>,
        Q: Eq + Hash,
    {
        self.map.get_full_mut2(item).map(|(_, k, v)| (k, &*v))
    }

    /// Returns the items not ordered
    pub fn into_vec(self) -> Vec<I> {
        self.map.into_iter().map(|(i, _)| i).collect()
    }
}

impl<I, P, H> PriorityQueue<I, P, H>
where
    P: Ord,
    I: Hash + Eq,
{
    /// Implements a HeapSort
    pub fn into_sorted_vec(mut self) -> Vec<I> {
        let mut res = Vec::with_capacity(self.size);
        while let Some((i, _)) = self.pop() {
            res.push(i);
        }
        res
    }

    /// Returns the number of elements in the priority queue.
    pub fn len(&self) -> usize {
        self.size
    }

    /// Returns true if the priority queue contains no elements.
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }
}

impl<I, P, H> PriorityQueue<I, P, H>
where
    P: Ord,
    I: Hash + Eq,
    H: BuildHasher,
{
    /// Drops all items from the priority queue
    pub fn clear(&mut self) {
        self.heap.clear();
        self.qp.clear();
        self.map.clear();
        self.size = 0;
    }

    /// Move all items of the `other` queue to `self`
    /// ignoring the items Eq to elements already in `self`
    /// At the end, `other` will be empty.
    ///
    /// **Note** that at the end, the priority of the duplicated elements
    /// inside self may be the one of the elements in other,
    /// if other is longer than self
    pub fn append(&mut self, other: &mut Self) {
        if other.size > self.size {
            ::std::mem::swap(self, other);
        }
        if other.size == 0 {
            return;
        }
        let drain = other.map.drain(..);
        // what should we do for duplicated keys?
        // ignore
        for (k, v) in drain {
            if !self.map.contains_key(&k) {
                let i = self.size;
                self.map.insert(k, v);
                self.heap.push(i);
                self.qp.push(i);
                self.size += 1;
            }
        }
        other.heap.clear();
        other.qp.clear();
        self.heap_build();
    }
}

impl<I, P, H> PriorityQueue<I, P, H>
where
    P: Ord,
    I: Hash + Eq,
{
    /// Generates a new iterator from self that
    /// will extract the elements from the one with the highest priority
    /// to the lowest one.
    pub fn into_sorted_iter(self) -> IntoSortedIter<I, P, H> {
        IntoSortedIter { pq: self }
    }
    /**************************************************************************/
    /*                            internal functions                          */

    /// Remove and return the element with the max priority
    /// and swap it with the last element keeping a consistent
    /// state.
    /// Computes in **O(1)** time (average)
    fn swap_remove(&mut self) -> Option<(I, P)> {
        // swap_remove the head
        let head = self.heap.swap_remove(0);
        self.size -= 1;
        // swap remove the old heap from the qp
        if self.size == 0 {
            self.qp.pop();
            return self.map.swap_remove_index(head);
        }
        unsafe {
            *self.qp.get_unchecked_mut(*self.heap.get_unchecked(0)) = 0;
        }
        self.qp.swap_remove(head);
        if head < self.size {
            unsafe {
                *self.heap.get_unchecked_mut(*self.qp.get_unchecked(head)) = head;
            }
        }
        // swap remove from the map and return to the client
        self.map.swap_remove_index(head)
    }

    /// Swap two elements keeping a consistent state.
    ///
    /// Computes in **O(1)** time (average)
    fn swap(&mut self, a: usize, b: usize) {
        let (i, j) = unsafe { (*self.heap.get_unchecked(a), *self.heap.get_unchecked(b)) };
        self.heap.swap(a, b);
        self.qp.swap(i, j);
    }

    /// Internal function that restore the functional property of the heap
    fn heapify(&mut self, i: usize) {
        let (mut l, mut r) = (left(i), right(i));
        let mut i = i;
        let mut largest = if l < self.size
            && unsafe {
                self.map.get_index(*self.heap.get_unchecked(l)).unwrap().1
                    > self.map.get_index(*self.heap.get_unchecked(i)).unwrap().1
            } {
            l
        } else {
            i
        };
        if r < self.size
            && unsafe {
                self.map.get_index(*self.heap.get_unchecked(r)).unwrap().1
                    > self
                        .map
                        .get_index(*self.heap.get_unchecked(largest))
                        .unwrap()
                        .1
            }
        {
            largest = r;
        }
        while largest != i {
            self.swap(i, largest);

            i = largest;
            l = left(i);
            r = right(i);
            if l < self.size
                && unsafe {
                    self.map.get_index(*self.heap.get_unchecked(l)).unwrap().1
                        > self.map.get_index(*self.heap.get_unchecked(i)).unwrap().1
                }
            {
                largest = l;
            } else {
                largest = i;
            }
            if r < self.size
                && unsafe {
                    self.map.get_index(*self.heap.get_unchecked(r)).unwrap().1
                        > self
                            .map
                            .get_index(*self.heap.get_unchecked(largest))
                            .unwrap()
                            .1
                }
            {
                largest = r;
            }
        }
    }

    /// Internal function that transform the `heap`
    /// vector in a heap with its properties
    pub(crate) fn heap_build(&mut self) {
        if self.size == 0 {
            return;
        }
        for i in (0..parent(self.size)).rev() {
            self.heapify(i);
        }
    }
}

//FIXME: fails when the vector contains repeated items
// FIXED: repeated items ignored
impl<I, P> From<Vec<(I, P)>> for PriorityQueue<I, P>
where
    I: Hash + Eq,
    P: Ord,
{
    fn from(vec: Vec<(I, P)>) -> Self {
        let mut pq = Self::with_capacity(vec.len());
        let mut i = 0;
        for (item, priority) in vec {
            if !pq.map.contains_key(&item) {
                pq.map.insert(item, priority);
                pq.qp.push(i);
                pq.heap.push(i);
                i += 1;
            }
        }
        pq.size = i;
        pq.heap_build();
        pq
    }
}

//FIXME: fails when the iterator contains repeated items
// FIXED: the item inside the pq is updated
// so there are two functions with different behaviours.
impl<I, P> ::std::iter::FromIterator<(I, P)> for PriorityQueue<I, P>
where
    I: Hash + Eq,
    P: Ord,
{
    fn from_iter<IT>(iter: IT) -> Self
    where
        IT: IntoIterator<Item = (I, P)>,
    {
        let iter = iter.into_iter();
        let (min, max) = iter.size_hint();
        let mut pq = if let Some(max) = max {
            Self::with_capacity_and_default_hasher(max)
        } else if min > 0 {
            Self::with_capacity_and_default_hasher(min)
        } else {
            Self::with_default_hasher()
        };
        for (item, priority) in iter {
            if pq.map.contains_key(&item) {
                let (_, old_item, old_priority) = pq.map.get_full_mut2(&item).unwrap();
                *old_item = item;
                *old_priority = priority;
            } else {
                pq.map.insert(item, priority);
                pq.qp.push(pq.size);
                pq.heap.push(pq.size);
                pq.size += 1;
            }
        }
        pq.heap_build();
        pq
    }
}

use ::std::iter::IntoIterator;
impl<I, P, H> IntoIterator for PriorityQueue<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher,
{
    type Item = (I, P);
    type IntoIter = crate::pqueue::IntoIter<I, P>;
    fn into_iter(self) -> crate::pqueue::IntoIter<I, P> {
        crate::pqueue::IntoIter {
            iter: self.map.into_iter(),
        }
    }
}

impl<'a, I, P, H> IntoIterator for &'a PriorityQueue<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher,
{
    type Item = (&'a I, &'a P);
    type IntoIter = Iter<'a, I, P>;
    fn into_iter(self) -> Iter<'a, I, P> {
        Iter {
            iter: self.map.iter(),
        }
    }
}

impl<'a, I, P, H> IntoIterator for &'a mut PriorityQueue<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
{
    type Item = (&'a mut I, &'a mut P);
    type IntoIter = IterMut<'a, I, P, H>;
    fn into_iter(self) -> IterMut<'a, I, P, H> {
        IterMut::new(self)
    }
}

impl<I, P, H> ::std::iter::Extend<(I, P)> for PriorityQueue<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher,
{
    fn extend<T: IntoIterator<Item = (I, P)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        let (min, max) = iter.size_hint();
        let mut rebuild = false;
        if let Some(max) = max {
            self.reserve(max);
            rebuild = better_to_rebuild(self.size, max);
        } else if min != 0 {
            self.reserve(min);
            rebuild = better_to_rebuild(self.size, min);
        }
        if rebuild {
            for (item, priority) in iter {
                if self.map.contains_key(&item) {
                    let (_, old_item, old_priority) = self.map.get_full_mut2(&item).unwrap();
                    *old_item = item;
                    *old_priority = priority;
                } else {
                    self.map.insert(item, priority);
                    self.qp.push(self.size);
                    self.heap.push(self.size);
                    self.size += 1;
                }
            }
            self.heap_build();
        } else {
            for (item, priority) in iter {
                self.push(item, priority);
            }
        }
    }
}

use std::fmt;
impl<I, P, H> fmt::Debug for PriorityQueue<I, P, H>
where
    I: fmt::Debug + Hash + Eq,
    P: fmt::Debug + Ord,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map()
            .entries(self.heap.iter().map(|&i| self.map.get_index(i).unwrap()))
            .finish()
    }
}

use std::cmp::PartialEq;

impl<I, P1, H1, P2, H2> PartialEq<PriorityQueue<I, P2, H2>> for PriorityQueue<I, P1, H1>
where
    I: Hash + Eq,
    P1: Ord,
    P1: PartialEq<P2>,
    Option<P1>: PartialEq<Option<P2>>,
    P2: Ord,
    H1: BuildHasher,
    H2: BuildHasher,
{
    fn eq(&self, other: &PriorityQueue<I, P2, H2>) -> bool {
        self.map == other.map
    }
}

/// Compute the index of the left child of an item from its index
fn left(i: usize) -> usize {
    (i * 2) + 1
}
/// Compute the index of the right child of an item from its index
fn right(i: usize) -> usize {
    (i * 2) + 2
}
/// Compute the index of the parent element in the heap from its index
fn parent(i: usize) -> usize {
    (i - 1) / 2
}

fn log2_fast(x: usize) -> usize {
    use std::mem::size_of;
    8 * size_of::<usize>() - (x.leading_zeros() as usize) - 1
}

// `rebuild` takes O(len1 + len2) operations
// and about 2 * (len1 + len2) comparisons in the worst case
// while `extend` takes O(len2 * log_2(len1)) operations
// and about 1 * len2 * log_2(len1) comparisons in the worst case,
// assuming len1 >= len2.
fn better_to_rebuild(len1: usize, len2: usize) -> bool {
    // log(1) == 0, so the inequation always falsy
    // log(0) is inapplicable and produces panic
    if len1 <= 1 {
        return false;
    }

    2 * (len1 + len2) < len2 * log2_fast(len1)
}

#[cfg(feature = "serde")]
mod serde {
    use crate::pqueue::PriorityQueue;

    use std::cmp::{Eq, Ord};
    use std::collections::hash_map::RandomState;
    use std::hash::{BuildHasher, Hash};
    use std::marker::PhantomData;

    use serde::ser::{Serialize, SerializeSeq, Serializer};
    impl<I, P, H> Serialize for PriorityQueue<I, P, H>
    where
        I: Hash + Eq + Serialize,
        P: Ord + Serialize,
        H: BuildHasher,
    {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let mut map_serializer = serializer.serialize_seq(Some(self.size))?;
            for (k, v) in &self.map {
                map_serializer.serialize_element(&(k, v))?;
            }
            map_serializer.end()
        }
    }

    use serde::de::{Deserialize, Deserializer, SeqAccess, Visitor};
    impl<'de, I, P, H> Deserialize<'de> for PriorityQueue<I, P, H>
    where
        I: Hash + Eq + Deserialize<'de>,
        P: Ord + Deserialize<'de>,
        H: BuildHasher + Default,
    {
        fn deserialize<D>(deserializer: D) -> Result<PriorityQueue<I, P, H>, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_seq(PQVisitor {
                marker: PhantomData,
            })
        }
    }

    struct PQVisitor<I, P, H = RandomState>
    where
        I: Hash + Eq,
        P: Ord,
    {
        marker: PhantomData<PriorityQueue<I, P, H>>,
    }
    impl<'de, I, P, H> Visitor<'de> for PQVisitor<I, P, H>
    where
        I: Hash + Eq + Deserialize<'de>,
        P: Ord + Deserialize<'de>,
        H: BuildHasher + Default,
    {
        type Value = PriorityQueue<I, P, H>;

        fn expecting(&self, formatter: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
            write!(formatter, "A priority queue")
        }

        fn visit_unit<E>(self) -> Result<Self::Value, E> {
            Ok(PriorityQueue::with_default_hasher())
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let mut pq: PriorityQueue<I, P, H> = if let Some(size) = seq.size_hint() {
                PriorityQueue::with_capacity_and_default_hasher(size)
            } else {
                PriorityQueue::with_default_hasher()
            };

            while let Some((item, priority)) = seq.next_element()? {
                pq.map.insert(item, priority);
                pq.qp.push(pq.size);
                pq.heap.push(pq.size);
                pq.size += 1;
            }
            pq.heap_build();
            Ok(pq)
        }
    }
}
