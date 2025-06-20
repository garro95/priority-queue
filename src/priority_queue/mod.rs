/*
 *  Copyright 2017 Gianmarco Garrisi
 *
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Lesser General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version, or (at your option) under the terms
 *  of the Mozilla Public License version 2.0.
 *
 *  ----
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 *  ----
 *
 *  This Source Code Form is subject to the terms of the Mozilla Public License,
 *  v. 2.0. If a copy of the MPL was not distributed with this file, You can
 *  obtain one at http://mozilla.org/MPL/2.0/.
 *
 */

//! This module contains the [`PriorityQueue`] type and the related iterators.
//!
//! See the type level documentation for more details and examples.

pub mod iterators;

#[cfg(not(feature = "std"))]
use std::vec::Vec;

use crate::better_to_rebuild;
use crate::core_iterators::*;
use crate::store::{left, parent, right};
use crate::store::{Index, Position, Store};
use crate::TryReserveError;
use iterators::*;

use std::borrow::Borrow;
use std::cmp::{Eq, Ord};
#[cfg(feature = "std")]
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash};
use std::iter::{Extend, FromIterator, IntoIterator, Iterator};
use std::mem::replace;

/// A priority queue with efficient change function to change the priority of an
/// element.
///
/// The priority is of type `P`, that must implement `std::cmp::Ord`.
///
/// The item is of type `I`, that must implement `Hash` and `Eq`.
///
/// Implemented as a heap of indexes, stores the items inside an `IndexMap`
/// to be able to retrieve them quickly.
///
/// # Example
/// ```rust
/// use priority_queue::PriorityQueue;
///
/// let mut pq = PriorityQueue::new();
///
/// assert!(pq.is_empty());
/// pq.push("Apples", 5);
/// pq.push("Bananas", 8);
/// pq.push("Strawberries", 23);
///
/// assert_eq!(pq.peek(), Some((&"Strawberries", &23)));
///
/// pq.change_priority("Bananas", 25);
/// assert_eq!(pq.peek(), Some((&"Bananas", &25)));
///
/// for (item, _) in pq.into_sorted_iter() {
///     println!("{}", item);
/// }
/// ```
#[derive(Clone, Debug)]
#[cfg(feature = "std")]
pub struct PriorityQueue<I, P, H = RandomState> {
    pub(crate) store: Store<I, P, H>,
}

#[derive(Clone, Debug)]
#[cfg(not(feature = "std"))]
pub struct PriorityQueue<I, P, H> {
    pub(crate) store: Store<I, P, H>,
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

#[cfg(feature = "std")]
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
            store: Store::with_capacity_and_hasher(capacity, hash_builder),
        }
    }
}

impl<I, P, H> PriorityQueue<I, P, H> {
    /// Returns an iterator in arbitrary order over the
    /// `(item, priority)` elements in the queue
    pub fn iter(&self) -> Iter<I, P> {
        self.store.iter()
    }

    /// Shrinks the capacity of the internal data structures
    /// that support this operation as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.store.shrink_to_fit();
    }

    /// Clears the `PriorityQueue`, returning an iterator over the removed elements in arbitrary order.
    /// If the iterator is dropped before being fully consumed, it drops the remaining elements in arbitrary order.
    pub fn drain(&mut self) -> Drain<I, P> {
        self.store.drain()
    }

    /// Returns the couple `(item, priority)` with the greatest
    /// priority in the queue, or `None` if it is empty.
    ///
    /// Computes in **O(1)** time
    pub fn peek(&self) -> Option<(&I, &P)> {
        self.store
            .heap
            .first()
            .and_then(|index| self.store.map.get_index(index.0))
    }

    /// Returns the number of elements the internal map can hold without
    /// reallocating.
    ///
    /// This number is a lower bound; the map might be able to hold more,
    /// but is guaranteed to be able to hold at least this many.
    pub fn capacity(&self) -> usize {
        self.store.capacity()
    }

    /// Returns the number of elements in the priority queue.
    #[inline]
    pub fn len(&self) -> usize {
        self.store.len()
    }

    /// Returns `true` if the priority queue contains no elements.
    pub fn is_empty(&self) -> bool {
        self.store.is_empty()
    }

    /// Returns the items not ordered
    pub fn into_vec(self) -> Vec<I> {
        self.store.into_vec()
    }

    /// Drops all items from the priority queue
    pub fn clear(&mut self) {
        self.store.clear();
    }

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
        self.store.reserve(additional);
    }

    /// Reserve capacity for `additional` more elements, without over-allocating.
    ///
    /// Unlike `reserve`, this does not deliberately over-allocate the entry capacity to avoid
    /// frequent re-allocations. However, the underlying data structures may still have internal
    /// capacity requirements, and the allocator itself may give more space than requested, so this
    /// cannot be relied upon to be precisely minimal.
    ///
    /// Computes in **O(n)** time.
    pub fn reserve_exact(&mut self, additional: usize) {
        self.store.reserve_exact(additional);
    }

    /// Try to reserve capacity for at least `additional` more elements.
    ///
    /// Computes in O(n) time.
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.store.try_reserve(additional)
    }

    /// Try to reserve capacity for `additional` more elements, without over-allocating.
    ///
    /// Unlike `reserve`, this does not deliberately over-allocate the entry capacity to avoid
    /// frequent re-allocations. However, the underlying data structures may still have internal
    /// capacity requirements, and the allocator itself may give more space than requested, so this
    /// cannot be relied upon to be precisely minimal.
    ///
    /// Computes in **O(n)** time.
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.store.try_reserve_exact(additional)
    }
}

impl<I, P, H> PriorityQueue<I, P, H>
where
    P: Ord,
{
    /// Returns an iterator in arbitrary order over the
    /// `(item, priority)` elements in the queue.
    ///
    /// The item and the priority are mutable references, but it's a logic error
    /// to modify the item in a way that change the result of `Hash` or `Eq`.
    ///
    /// It's *not* an error, instead, to modify the priorities, because the heap
    /// will be rebuilt once the `IterMut` goes out of scope.
    ///
    /// It would be rebuilt even if no priority value would have been modified,
    /// but the procedure will not move anything, but just compare the priorities.
    pub fn iter_mut(&mut self) -> IterMut<I, P, H> {
        IterMut::new(self)
    }

    /// Removes the item with the greatest priority from
    /// the priority queue and returns the pair `(item, priority)`,
    /// or `None` if the queue is empty.
    pub fn pop(&mut self) -> Option<(I, P)> {
        match self.len() {
            0 => None,
            1 => self.store.swap_remove(Position(0)),
            _ => {
                let r = self.store.swap_remove(Position(0));
                self.heapify(Position(0));
                r
            }
        }
    }

    /// Implements a heap sort.
    ///
    /// Returns a `Vec<I>` sorted from the item associated to the highest priority to the lowest.
    pub fn into_sorted_vec(mut self) -> Vec<I> {
        let mut res = Vec::with_capacity(self.store.size);
        while let Some((i, _)) = self.pop() {
            res.push(i);
        }
        res
    }

    /// Generates a new iterator from `self` that
    /// will extract the elements from the one with the highest priority
    /// to the lowest one.
    pub fn into_sorted_iter(self) -> IntoSortedIter<I, P, H> {
        IntoSortedIter { pq: self }
    }
}

impl<I, P, H> PriorityQueue<I, P, H>
where
    P: Ord,
    I: Hash + Eq,
    H: BuildHasher,
{
    /// Retains only the elements specified by the `predicate`.
    ///
    /// In other words, remove all elements e for which `predicate(&i, &p)` returns `false`.
    /// The elements are visited in arbitrary order.
    pub fn retain<F>(&mut self, predicate: F)
    where
        F: FnMut(&I, &P) -> bool,
    {
        self.store.retain(predicate);
        self.heap_build();
    }

    /// Retains only the elements specified by the `predicate`.
    ///
    /// In other words, remove all elements e for which `predicate(&mut i, &mut p)` returns `false`.
    /// The elements are visited in arbitrary order.
    ///
    /// The `predicate` receives mutable references to both the item and
    /// the priority.
    ///
    /// It's a logical error to change the item in a way
    /// that changes the result of `Hash` or `Eq`.
    ///
    /// The `predicate` can change the priority. If the element is retained,
    /// it will have the updated one.
    pub fn retain_mut<F>(&mut self, predicate: F)
    where
        F: FnMut(&mut I, &mut P) -> bool,
    {
        self.store.retain_mut(predicate);
        self.heap_build();
    }

    /// Returns an `Iterator` removing from the queue the `(item, priority)`
    /// pairs for which the `predicate` returns `true`, in arbitraty order.
    ///
    /// The `predicate` receives mutable references to both the item and
    /// the priority.
    ///
    /// It's a logical error to change the item in a way
    /// that changes the result of `Hash` or `Eq`.
    ///
    /// The `predicate` can change the priority. If it returns `true`, the
    /// extracted pair will have the updated priority, otherwise, the
    /// heap structural property will be restored once the iterator is `Drop`ped.
    ///
    /// # Example
    /// ```
    /// # use priority_queue::PriorityQueue;
    /// let mut pq = PriorityQueue::new();
    ///
    /// pq.push("Apples", 5);
    /// pq.push("Bananas", 10);
    ///
    /// assert_eq!(pq.extract_if(|i, p| {
    ///   *p = 15;
    ///   i == &"Apples"
    /// }).collect::<Vec<_>>(), vec![("Apples", 15)]);
    ///
    /// assert_eq!(pq.peek(), Some((&"Bananas", &15)));
    /// assert_eq!(pq.into_vec(), vec!["Bananas"]);
    /// ```
    pub fn extract_if<F>(&mut self, predicate: F) -> ExtractIf<I, P, F, H>
    where
        F: FnMut(&mut I, &mut P) -> bool,
    {
        ExtractIf::new(self, predicate)
    }

    /// Removes the item with the greatest priority from
    /// the priority queue if the `predicate` returns `true`.
    ///
    /// Returns the pair `(item, priority)`, or `None` if the
    /// queue is empty or the `predicate` returns `false`.
    ///
    /// The `predicate` receives mutable references to both the item
    /// and the priority.
    ///
    /// It's a logical error to change the item in a way
    /// that changes the result of `Hash` or `Eq`.
    ///
    /// The `predicate` can change the priority. If it returns `true`,
    /// the returned couple will have the updated priority,
    /// otherwise, the heap structural property will be restored.
    ///
    /// # Example
    /// ```
    /// # use priority_queue::PriorityQueue;
    /// let mut pq = PriorityQueue::new();
    ///
    /// pq.push("Apples", 5);
    /// pq.push("Bananas", 10);
    ///
    /// assert_eq!(pq.pop_if(|i, p| {
    ///   *p = 3;
    ///   false
    /// }), None);
    ///
    /// assert_eq!(pq.pop(), Some(("Apples", 5)));
    /// ```
    pub fn pop_if<F>(&mut self, predicate: F) -> Option<(I, P)>
    where
        F: FnOnce(&mut I, &mut P) -> bool,
    {
        match self.len() {
            0 => None,
            1 => self.store.swap_remove_if(Position(0), predicate),
            _ => {
                let r = self.store.swap_remove_if(Position(0), predicate);
                self.heapify(Position(0));
                r
            }
        }
    }

    /// Insert the `(item, priority)` pair into the queue.
    ///
    /// If an element equal to `item` is already in the queue, its priority
    /// is updated and the old priority is returned in `Some`; otherwise,
    /// `item` is inserted with `priority` and `None` is returned.
    ///
    /// # Example
    /// ```
    /// # use priority_queue::PriorityQueue;
    /// let mut pq = PriorityQueue::new();
    /// assert_eq!(pq.push("Apples", 5), None);
    /// assert_eq!(pq.get_priority("Apples"), Some(&5));
    /// assert_eq!(pq.push("Apples", 6), Some(5));
    /// assert_eq!(pq.get_priority("Apples"), Some(&6));
    /// assert_eq!(pq.push("Apples", 4), Some(6));
    /// assert_eq!(pq.get_priority("Apples"), Some(&4));
    /// ```
    ///
    /// Computes in **O(log(N))** time.
    pub fn push(&mut self, item: I, priority: P) -> Option<P> {
        use indexmap::map::Entry::*;
        let mut pos = Position(0);
        let mut oldp = None;

        match self.store.map.entry(item) {
            Occupied(mut e) => {
                oldp = Some(replace(e.get_mut(), priority));
                pos = unsafe { *self.store.qp.get_unchecked(e.index()) };
            }
            Vacant(e) => {
                e.insert(priority);
            }
        }

        if oldp.is_some() {
            self.up_heapify(pos);
            return oldp;
        }
        // copy the current size of the heap
        let i = self.len();
        // add the new element in the qp vector as the last in the heap
        self.store.qp.push(Position(i));
        self.store.heap.push(Index(i));
        self.bubble_up(Position(i), Index(i));
        self.store.size += 1;
        None
    }

    /// Increase the priority of an existing item in the queue, or
    /// insert it if not present.
    ///
    /// If an element equal to `item` is already in the queue with a
    /// lower priority, its priority is increased to the new one
    /// without replacing the element and the old priority is returned
    /// in `Some`.
    ///
    /// If an element equal to `item` is already in the queue with an
    /// equal or higher priority, its priority is not changed and the
    /// `priority` argument is returned in `Some`.
    ///
    /// If no element equal to `item` is already in the queue, the new
    /// element is inserted and `None` is returned.
    ///
    /// # Example
    /// ```
    /// # use priority_queue::PriorityQueue;
    /// let mut pq = PriorityQueue::new();
    /// assert_eq!(pq.push_increase("Apples", 5), None);
    /// assert_eq!(pq.get_priority("Apples"), Some(&5));
    /// assert_eq!(pq.push_increase("Apples", 6), Some(5));
    /// assert_eq!(pq.get_priority("Apples"), Some(&6));
    /// // Already present with higher priority, so requested (lower)
    /// // priority is returned.
    /// assert_eq!(pq.push_increase("Apples", 4), Some(4));
    /// assert_eq!(pq.get_priority("Apples"), Some(&6));
    /// ```
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
    /// without replacing the element and the old priority is returned
    /// in `Some`.
    ///
    /// If an element equal to `item` is already in the queue with an
    /// equal or lower priority, its priority is not changed and the
    /// `priority` argument is returned in `Some`.
    ///
    /// If no element equal to `item` is already in the queue, the new
    /// element is inserted and `None` is returned.
    ///
    /// # Example
    /// ```
    /// # use priority_queue::PriorityQueue;
    /// let mut pq = PriorityQueue::new();
    /// assert_eq!(pq.push_decrease("Apples", 5), None);
    /// assert_eq!(pq.get_priority("Apples"), Some(&5));
    /// assert_eq!(pq.push_decrease("Apples", 4), Some(5));
    /// assert_eq!(pq.get_priority("Apples"), Some(&4));
    /// // Already present with lower priority, so requested (higher)
    /// // priority is returned.
    /// assert_eq!(pq.push_decrease("Apples", 6), Some(6));
    /// assert_eq!(pq.get_priority("Apples"), Some(&4));
    /// ```
    ///
    /// Computes in **O(log(N))** time.
    pub fn push_decrease(&mut self, item: I, priority: P) -> Option<P> {
        if self.get_priority(&item).map_or(true, |p| priority < *p) {
            self.push(item, priority)
        } else {
            Some(priority)
        }
    }

    /// Change the priority of an item returning the old value of priority,
    /// or `None` if the item wasn't in the queue.
    ///
    /// The argument `item` is only used for lookup, and is not used to overwrite the item's data
    /// in the priority queue.
    ///
    /// # Example
    /// ```
    /// # use priority_queue::PriorityQueue;
    /// let mut pq = PriorityQueue::new();
    /// assert_eq!(pq.change_priority("Apples", 5), None);
    /// assert_eq!(pq.get_priority("Apples"), None);
    /// assert_eq!(pq.push("Apples", 6), None);
    /// assert_eq!(pq.get_priority("Apples"), Some(&6));
    /// assert_eq!(pq.change_priority("Apples", 4), Some(6));
    /// assert_eq!(pq.get_priority("Apples"), Some(&4));
    /// ```
    ///
    /// The item is found in **O(1)** thanks to the hash table.
    /// The operation is performed in **O(log(N))** time.
    pub fn change_priority<Q>(&mut self, item: &Q, new_priority: P) -> Option<P>
    where
        I: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.store
            .change_priority(item, new_priority)
            .map(|(r, pos)| {
                self.up_heapify(pos);
                r
            })
    }

    /// Change the priority of an item using the provided function.
    ///
    /// Returns a boolean value where `true` means the item was in the queue and update was successful.
    ///
    /// The argument `item` is only used for lookup, and is not used to overwrite the item's data
    /// in the priority queue.
    ///
    /// The item is found in **O(1)** thanks to the hash table.
    /// The operation is performed in **O(log(N))** time (worst case).
    pub fn change_priority_by<Q, F>(&mut self, item: &Q, priority_setter: F) -> bool
    where
        I: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
        F: FnOnce(&mut P),
    {
        self.store
            .change_priority_by(item, priority_setter)
            .map(|pos| {
                self.up_heapify(pos);
            })
            .is_some()
    }

    /// Get the priority of an item, or `None`, if the item is not in the queue
    pub fn get_priority<Q>(&self, item: &Q) -> Option<&P>
    where
        I: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.store.get_priority(item)
    }

    /// Check if the queue contains `item`.
    ///
    /// Returns `true` if `item` is in the queue, `false` if it is not.
    pub fn contains<Q>(&self, item: &Q) -> bool
    where
        I: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.store.contains(item)
    }

    /// Get the couple `(item, priority)` of an arbitrary element, as reference
    /// or `None` if the item is not in the queue.
    pub fn get<Q>(&self, item: &Q) -> Option<(&I, &P)>
    where
        I: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.store.get(item)
    }

    /// Get the couple `(item, priority)` of an arbitrary element, or `None`
    /// if the item was not in the queue.
    ///
    /// The item is a mutable reference, but it's a logic error to modify it
    /// in a way that change the result of  `Hash` or `Eq`.
    ///
    /// The priority cannot be modified with a call to this function.
    /// To modify the priority use [`push`](PriorityQueue::push),
    /// [`change_priority`](PriorityQueue::change_priority) or
    /// [`change_priority_by`](PriorityQueue::change_priority_by).
    pub fn get_mut<Q>(&mut self, item: &Q) -> Option<(&mut I, &P)>
    where
        I: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.store.get_mut(item)
    }

    /// Returns the couple `(item, priority)` with the greatest
    /// priority in the queue, or `None` if it is empty.
    ///
    /// The item is a mutable reference, but it's a logic error to modify it
    /// in a way that change the result of  `Hash` or `Eq`.
    ///
    /// The priority cannot be modified with a call to this function.
    /// To modify the priority use[`push`](PriorityQueue::push),
    /// [`change_priority`](PriorityQueue::change_priority) or
    /// [`change_priority_by`](PriorityQueue::change_priority_by).
    ///
    /// Computes in **O(1)** time
    pub fn peek_mut(&mut self) -> Option<(&mut I, &P)> {
        use indexmap::map::MutableKeys;
        if self.store.size == 0 {
            return None;
        }
        self.store
            .map
            .get_index_mut2(unsafe { self.store.heap.get_unchecked(0) }.0)
            .map(|(k, v)| (k, &*v))
    }

    /// Remove an arbitrary element from the priority queue.
    ///
    /// Returns the `(item, priority)` couple or `None` if the item
    /// is not found in the queue.
    ///
    /// The operation is performed in **O(log(N))** time (worst case).
    pub fn remove<Q>(&mut self, item: &Q) -> Option<(I, P)>
    where
        I: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.store.remove(item).map(|(item, priority, pos)| {
            if pos.0 < self.len() {
                self.up_heapify(pos);
            }

            (item, priority)
        })
    }

    /// Move all items of the `other` queue to `self`
    /// ignoring the items Eq to elements already in `self`
    /// At the end, `other` will be empty.
    ///
    /// **Note** that at the end, the priority of the duplicated elements
    /// inside `self` may be the one of the elements in `other`,
    /// if `other` is longer than `self`
    pub fn append(&mut self, other: &mut Self) {
        self.store.append(&mut other.store);
        self.heap_build();
    }
}

impl<I, P, H> PriorityQueue<I, P, H>
where
    P: Ord,
{
    /**************************************************************************/
    /*                            internal functions                          */

    /// Internal function that restores the functional property of the sub-heap rooted in `i`
    ///
    /// Computes in **O(log(N))** time
    fn heapify(&mut self, mut i: Position) {
        if self.len() <= 1 {
            return;
        }

        let (mut l, mut r) = (left(i), right(i));
        let mut largest = i;

        let mut largestp = unsafe { self.store.get_priority_from_position(i) };
        if l.0 < self.len() {
            let childp = unsafe { self.store.get_priority_from_position(l) };
            if childp > largestp {
                largest = l;
                largestp = childp;
            }

            if r.0 < self.len() && unsafe { self.store.get_priority_from_position(r) } > largestp {
                largest = r;
            }
        }

        while largest != i {
            self.store.swap(i, largest);

            i = largest;
            largestp = unsafe { self.store.get_priority_from_position(i) };
            l = left(i);
            if l.0 < self.len() {
                let childp = unsafe { self.store.get_priority_from_position(l) };
                if childp > largestp {
                    largest = l;
                    largestp = childp;
                }

                r = right(i);
                if r.0 < self.len()
                    && unsafe { self.store.get_priority_from_position(r) } > largestp
                {
                    largest = r;
                }
            }
        }
    }

    /// from the leaf go up to root or until an element with priority greater
    /// than the new element is found
    fn bubble_up(&mut self, mut position: Position, map_position: Index) -> Position {
        let priority = self.store.map.get_index(map_position.0).unwrap().1;
        let mut parent_position = Position(0);
        while if position.0 > 0 {
            parent_position = parent(position);
            (unsafe { self.store.get_priority_from_position(parent_position) }) < priority
        } else {
            false
        } {
            unsafe {
                let parent_index = *self.store.heap.get_unchecked(parent_position.0);
                *self.store.heap.get_unchecked_mut(position.0) = parent_index;
                *self.store.qp.get_unchecked_mut(parent_index.0) = position;
            }
            position = parent_position;
        }
        unsafe {
            *self.store.heap.get_unchecked_mut(position.0) = map_position;
            *self.store.qp.get_unchecked_mut(map_position.0) = position;
        }
        position
    }

    /// Internal function that moves a leaf in position `i` to its correct place in the heap
    /// and restores the functional property
    ///
    /// Computes in **O(log(N))**
    fn up_heapify(&mut self, i: Position) {
        let tmp = unsafe { *self.store.heap.get_unchecked(i.0) };
        let pos = self.bubble_up(i, tmp);
        self.heapify(pos)
    }

    /// Internal function that transform the `heap`
    /// vector in a heap with its properties
    ///
    /// Computes in **O(N)**
    pub(crate) fn heap_build(&mut self) {
        if self.is_empty() {
            return;
        }
        for i in (0..=parent(Position(self.len())).0).rev() {
            self.heapify(Position(i));
        }
    }
}

//FIXME: fails when the vector contains repeated items
// FIXED: repeated items ignored
impl<I, P, H> From<Vec<(I, P)>> for PriorityQueue<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher + Default,
{
    fn from(vec: Vec<(I, P)>) -> Self {
        let store = Store::from(vec);
        let mut pq = PriorityQueue { store };
        pq.heap_build();
        pq
    }
}

use crate::DoublePriorityQueue;

impl<I, P, H> From<DoublePriorityQueue<I, P, H>> for PriorityQueue<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher,
{
    fn from(pq: DoublePriorityQueue<I, P, H>) -> Self {
        let store = pq.store;
        let mut this = Self { store };
        this.heap_build();
        this
    }
}

//FIXME: fails when the iterator contains repeated items
// FIXED: the item inside the pq is updated
// so there are two functions with different behaviours.
impl<I, P, H> FromIterator<(I, P)> for PriorityQueue<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher + Default,
{
    fn from_iter<IT>(iter: IT) -> Self
    where
        IT: IntoIterator<Item = (I, P)>,
    {
        let store = Store::from_iter(iter);
        let mut pq = PriorityQueue { store };
        pq.heap_build();
        pq
    }
}

impl<I, P, H> IntoIterator for PriorityQueue<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher,
{
    type Item = (I, P);
    type IntoIter = IntoIter<I, P>;
    fn into_iter(self) -> IntoIter<I, P> {
        self.store.into_iter()
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
        self.store.iter()
    }
}

impl<'a, I, P, H> IntoIterator for &'a mut PriorityQueue<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher,
{
    type Item = (&'a mut I, &'a mut P);
    type IntoIter = IterMut<'a, I, P, H>;
    fn into_iter(self) -> IterMut<'a, I, P, H> {
        IterMut::new(self)
    }
}

impl<I, P, H> Extend<(I, P)> for PriorityQueue<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher,
{
    fn extend<T: IntoIterator<Item = (I, P)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        let (min, max) = iter.size_hint();
        let rebuild = if let Some(max) = max {
            self.reserve(max);
            better_to_rebuild(self.len(), max)
        } else if min != 0 {
            self.reserve(min);
            better_to_rebuild(self.len(), min)
        } else {
            false
        };
        if rebuild {
            self.store.extend(iter);
            self.heap_build();
        } else {
            for (item, priority) in iter {
                self.push(item, priority);
            }
        }
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
        self.store == other.store
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
mod serde {
    use std::cmp::{Eq, Ord};
    use std::hash::{BuildHasher, Hash};

    use serde::de::{Deserialize, Deserializer};
    use serde::ser::{Serialize, Serializer};

    use super::PriorityQueue;
    use crate::store::Store;

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
            self.store.serialize(serializer)
        }
    }

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
            Store::deserialize(deserializer).map(|store| {
                let mut pq = PriorityQueue { store };
                pq.heap_build();
                pq
            })
        }
    }
}
