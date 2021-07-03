/*
 *  Copyright 2017 Gianmarco Garrisi
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
#[cfg(not(has_std))]
use std::vec::Vec;

// an improvement in terms of complexity would be to use a bare HashMap
// as vec instead of the IndexMap
use crate::core_iterators::*;

use std::borrow::Borrow;
use std::cmp::{Eq, Ord};
#[cfg(has_std)]
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash};
use std::iter::{FromIterator, IntoIterator, Iterator};

use indexmap::map::{IndexMap, MutableKeys};

/// Internal storage of PriorityQueue and DoublePriorityQueue
#[derive(Clone)]
#[cfg(has_std)]
pub(crate) struct Store<I, P, H = RandomState>
where
    I: Hash + Eq,
    P: Ord,
{
    pub map: IndexMap<I, P, H>, // Stores the items and assign them an index
    pub heap: Vec<usize>,       // Implements the heap of indexes
    pub qp: Vec<usize>,         // Performs the translation from the index
    // of the map to the index of the heap
    pub size: usize, // The size of the heap
}

#[derive(Clone)]
#[cfg(not(has_std))]
pub(crate) struct Store<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
{
    pub map: IndexMap<I, P, H>, // Stores the items and assign them an index
    pub heap: Vec<usize>,       // Implements the heap of indexes
    pub qp: Vec<usize>,         // Performs the translation from the index
    // of the map to the index of the heap
    pub size: usize, // The size of the heap
}

// do not [derive(Eq)] to loosen up trait requirements for other types and impls
impl<I, P, H> Eq for Store<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher,
{
}

impl<I, P, H> Default for Store<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher + Default,
{
    fn default() -> Self {
        Self::with_default_hasher()
    }
}

#[cfg(has_std)]
impl<I, P> Store<I, P>
where
    P: Ord,
    I: Hash + Eq,
{
    /// Creates an empty `Store`
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Creates an empty `Store` with the specified capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_default_hasher(capacity)
    }
}

impl<I, P, H> Store<I, P, H>
where
    P: Ord,
    I: Hash + Eq,
    H: BuildHasher + Default,
{
    /// Creates an empty `Store` with the default hasher
    pub fn with_default_hasher() -> Self {
        Self::with_capacity_and_default_hasher(0)
    }

    /// Creates an empty `Store` with the specified capacity and default hasher
    pub fn with_capacity_and_default_hasher(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, H::default())
    }
}

impl<I, P, H> Store<I, P, H>
where
    P: Ord,
    I: Hash + Eq,
    H: BuildHasher,
{
    /// Creates an empty `Store` with the specified hasher
    pub fn with_hasher(hash_builder: H) -> Self {
        Self::with_capacity_and_hasher(0, hash_builder)
    }

    /// Creates an empty `Store` with the specified capacity and hasher
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
    pub fn iter(&self) -> Iter<I, P> {
        Iter {
            iter: self.map.iter(),
        }
    }
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

/*
impl<I, P, H> Store<I, P, H>
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
}
*/

impl<I, P, H> Store<I, P, H>
where
    P: Ord,
    I: Hash + Eq,
{
    /// Returns the number of elements the internal map can hold without
    /// reallocating.
    ///
    /// This number is a lower bound; the map might be able to hold more,
    /// but is guaranteed to be able to hold at least this many.
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// Shrinks the capacity of the internal data structures
    /// that support this operation as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.heap.shrink_to_fit();
        self.qp.shrink_to_fit();
    }

    /// Returns the number of elements in the priority queue.
    pub fn len(&self) -> usize {
        self.size
    }

    /// Returns true if the priority queue contains no elements.
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Swap two elements keeping a consistent state.
    ///
    /// Computes in **O(1)** time
    pub fn swap(&mut self, a: usize, b: usize) {
        let (i, j) = unsafe {
            (
                *self.heap.get_unchecked(a),
                *self.heap.get_unchecked(b),
            )
        };
        self.heap.swap(a, b);
        self.qp.swap(i, j);
    }
    
    /// Remove and return the element with the max priority
    /// and swap it with the last element keeping a consistent
    /// state.
    ///
    /// Computes in **O(1)** time (average)
    pub fn swap_remove(&mut self, index: usize) -> Option<(I, P)> {
        // swap_remove the head
        let head = self.heap.swap_remove(index);
        self.size -= 1;
        // swap remove the old heap head from the qp
        if self.size == 0 {
            self.qp.pop();
            return self.map.swap_remove_index(head);
        }
        unsafe {
            *self
                .qp
                .get_unchecked_mut(*self.heap.get_unchecked(0)) = 0;
        }
        self.qp.swap_remove(head);
        if head < self.size {
            unsafe {
                *self
                    .heap
                    .get_unchecked_mut(*self.qp.get_unchecked(head)) = head;
            }
        }
        // swap remove from the map and return to the client
        self.map.swap_remove_index(head)
    }
}

impl<I, P, H> Store<I, P, H>
where
    P: Ord,
    I: Hash + Eq,
    H: BuildHasher,
{
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
    pub fn get<Q: ?Sized>(&self, item: &Q) -> Option<(&I, &P)>
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
    pub fn get_mut<Q: ?Sized>(&mut self, item: &Q) -> Option<(&mut I, &P)>
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

    /// Drops all items from the priority queue
    pub fn clear(&mut self) {
        self.heap.clear();
        self.qp.clear();
        self.map.clear();
        self.size = 0;
    }
}

impl<I, P, H> IntoIterator for Store<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher,
{
    type Item = (I, P);
    type IntoIter = IntoIter<I, P>;
    fn into_iter(self) -> IntoIter<I, P> {
        IntoIter {
            iter: self.map.into_iter(),
        }
    }
}

impl<'a, I, P, H> IntoIterator for &'a Store<I, P, H>
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

use std::cmp::PartialEq;

impl<I, P1, H1, P2, H2> PartialEq<Store<I, P2, H2>> for Store<I, P1, H1>
where
    I: Hash + Eq,
    P1: Ord,
    P1: PartialEq<P2>,
    Option<P1>: PartialEq<Option<P2>>,
    P2: Ord,
    H1: BuildHasher,
    H2: BuildHasher,
{
    fn eq(&self, other: &Store<I, P2, H2>) -> bool {
        self.map == other.map
    }
}

impl<I, P, H> From<Vec<(I, P)>> for Store<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher + Default,
{
    fn from(vec: Vec<(I, P)>) -> Self {
        let mut store = Self::with_capacity_and_hasher(vec.len(), <_>::default());
        let mut i = 0;
        for (item, priority) in vec {
            if !store.map.contains_key(&item) {
                store.map.insert(item, priority);
                store.qp.push(i);
                store.heap.push(i);
                i += 1;
            }
        }
        store.size = i;
        store
    }
}

impl<I, P, H> FromIterator<(I, P)> for Store<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher + Default,
{
    fn from_iter<IT>(iter: IT) -> Self
    where
        IT: IntoIterator<Item = (I, P)>,
    {
        let iter = iter.into_iter();
        let (min, max) = iter.size_hint();
        let mut store = if let Some(max) = max {
            Self::with_capacity_and_hasher(max, <_>::default())
        } else if min > 0 {
            Self::with_capacity_and_hasher(min, <_>::default())
        } else {
            Self::with_hasher(<_>::default())
        };
        for (item, priority) in iter {
            if store.map.contains_key(&item) {
                let (_, old_item, old_priority) = store.map.get_full_mut2(&item).unwrap();
                *old_item = item;
                *old_priority = priority;
            } else {
                store.map.insert(item, priority);
                store.qp.push(store.size);
                store.heap.push(store.size);
                store.size += 1;
            }
        }
        store
    }
}

impl<I, P, H> Extend<(I, P)> for Store<I, P, H>
where
    I: Hash + Eq,
    P: Ord,
    H: BuildHasher,
{
    fn extend<T: IntoIterator<Item = (I, P)>>(&mut self, iter: T) {
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
    }
}

#[cfg(feature = "serde")]
mod serde {
    use crate::store::Store;

    use std::cmp::{Eq, Ord};
    use std::collections::hash_map::RandomState;
    use std::hash::{BuildHasher, Hash};
    use std::marker::PhantomData;

    use serde::ser::{Serialize, SerializeSeq, Serializer};

    impl<I, P, H> Serialize for Store<I, P, H>
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
    impl<'de, I, P, H> Deserialize<'de> for Store<I, P, H>
    where
        I: Hash + Eq + Deserialize<'de>,
        P: Ord + Deserialize<'de>,
        H: BuildHasher + Default,
    {
        fn deserialize<D>(deserializer: D) -> Result<Store<I, P, H>, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_seq(StoreVisitor {
                marker: PhantomData,
            })
        }
    }

    struct StoreVisitor<I, P, H = RandomState>
    where
        I: Hash + Eq,
        P: Ord,
    {
        marker: PhantomData<Store<I, P, H>>,
    }
    impl<'de, I, P, H> Visitor<'de> for StoreVisitor<I, P, H>
    where
        I: Hash + Eq + Deserialize<'de>,
        P: Ord + Deserialize<'de>,
        H: BuildHasher + Default,
    {
        type Value = Store<I, P, H>;

        fn expecting(&self, formatter: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
            write!(formatter, "A priority queue")
        }

        fn visit_unit<E>(self) -> Result<Self::Value, E> {
            Ok(Store::with_default_hasher())
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let mut store: Store<I, P, H> = if let Some(size) = seq.size_hint() {
                Store::with_capacity_and_default_hasher(size)
            } else {
                Store::with_default_hasher()
            };

            while let Some((item, priority)) = seq.next_element()? {
                store.map.insert(item, priority);
                store.qp.push(store.size);
                store.heap.push(store.size);
                store.size += 1;
            }
            Ok(store)
        }
    }
}
