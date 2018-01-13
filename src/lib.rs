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

//! This crate provide a priority queue backed by an hashmap
//! with some efficient methods to change the priority of an element in
//! **O(log(N))** time (worst case).
//! 
//! The elements(called `Item`s, of type `I`) must implement [`Hash`]
//! (https://doc.rust-lang.org/std/hash/trait.Hash.html)
//! and [`Eq`](https://doc.rust-lang.org/std/cmp/trait.Eq.html) traits.
//! 
//! The priority `P` may be any type that implements [`Ord`]
//! (https://doc.rust-lang.org/std/cmp/trait.Ord.html).
//! For reverse order remember the standard wrapper [`Reverse<T>`]
//! (https://doc.rust-lang.org/std/cmp/struct.Reverse.html)
//! 
//! #Example
//! ```rust
//! extern crate priority_queue;
//! 
//! use priority_queue::PriorityQueue;
//!       
//! fn main() {
//!     let mut pq = PriorityQueue::new();
//! 
//!     assert!(pq.is_empty());
//!     pq.push("Apples", 5);
//!     pq.push("Bananas", 8);
//!     pq.push("Strawberries", 23);
//! 
//!     assert_eq!(pq.peek(), Some((&"Strawberries", &23)));
//!     
//!     pq.change_priority("Bananas", 25);
//!     assert_eq!(pq.peek(), Some((&"Bananas", &25)));
//! 
//!     for (item, _) in pq.into_sorted_iter() {
//!         println!("{}", item);
//!     }
//! }
//! ```

extern crate ordermap;
#[cfg(all(feature = "serde", test))]
#[macro_use]
extern crate serde_derive;
mod pqueue;
mod iterators;
pub use pqueue::PriorityQueue;

#[cfg(test)]
mod tests {
    pub use PriorityQueue;

    #[test]
    fn init(){
        let pq: PriorityQueue<String, i32> = PriorityQueue::new();
        println!("{:?}", pq);
    }

    #[test]
    fn push_len() {
        let mut pq = PriorityQueue::new();
        pq.push("a", 1);
        pq.push("b", 2);
        println!("{:?}", pq);
        assert_eq!(pq.len(), 2);
    }

    #[test]
    fn push_pop() {
        let mut pq = PriorityQueue::new();
        assert_eq!(pq.peek(), None);
        pq.push("a", 1);
        pq.push("b", 2);
        pq.push("f", 7);
        pq.push("g", 4);
        pq.push("h", 3);
        println!("{:?}", pq);
        assert_eq!(pq.pop(), Some(("f", 7)));
        println!("{:?}", pq);
        assert_eq!(pq.peek(), Some((&"g", &4)));
        assert_eq!(pq.pop(), Some(("g", 4)));
        assert_eq!(pq.len(), 3);
    }

    #[test]
    fn push_update() {
        let mut pq = PriorityQueue::new();
        pq.push("a", 9);
        pq.push("b", 8);
        pq.push("c", 7);
        pq.push("d", 6);
        pq.push("e", 5);
        pq.push("f", 4);
        pq.push("g", 10);
        pq.push("k", 11);

        pq.push("d", 20);
        assert_eq!(pq.peek(), Some((&"d", &20)));
        assert_eq!(pq.pop(), Some(("d", 20)));
    }
    
    #[test]
    fn change_priority() {
        let mut pq = PriorityQueue::new();
        pq.push("Processor", 1);
        pq.push("Mainboard", 2);
        pq.push("RAM", 5);
        pq.push("GPU", 4);
        pq.push("Disk", 3);
        pq.change_priority("Processor", 10);
        assert_eq!(pq.peek(), Some((&"Processor", &10)));

        pq.change_priority("RAM", 11);
        assert_eq!(pq.peek(), Some((&"RAM", &11)));
    }

    #[test]
    fn from_vec() {
        let v = vec!(("a", 1), ("b", 2), ("f", 7));
        let mut pq = PriorityQueue::from(v);
        assert_eq!(pq.pop(), Some(("f", 7)));
        assert_eq!(pq.len(), 2);
    }
    
    #[test]
    fn from_vec_with_repeated() {
        let v = vec!(("a", 1), ("b", 2), ("f", 7), ("a", 2));
        let mut pq = PriorityQueue::from(v);
        assert_eq!(pq.pop(), Some(("f", 7)));
        assert_eq!(pq.len(), 2);
    }

    #[test]
    fn from_iter() {
        use std::iter::FromIterator;
        
        let v = vec!(("a", 1), ("b", 2), ("f", 7));
        let mut pq = PriorityQueue::from_iter(v.into_iter());
        assert_eq!(pq.pop(), Some(("f", 7)));
        assert_eq!(pq.len(), 2);
    }

    #[test]
    fn heap_sort() {
        let v = vec!(("a", 2), ("b", 7), ("f", 1));
        let sorted = (PriorityQueue::from(v)).into_sorted_vec();
        assert_eq!(sorted.as_slice(), &["b", "a", "f"]);
    }

    #[test]
    fn change_priority_by() {
        use std::iter::FromIterator;
        
        let v = vec!(("a", 1), ("b", 2), ("f", 7), ("g", 6), ("h", 5));
        let mut pq = PriorityQueue::from_iter(v.into_iter());

        pq.change_priority_by("b", |b| b+8);
        assert_eq!(pq.into_sorted_vec().as_slice(), &["b", "f", "g", "h", "a"]);
    }

    #[test]
    fn extend() {
        let mut pq = PriorityQueue::new();
        pq.push("a", 1);
        pq.push("b", 2);
        pq.push("f", 7);

        let v = vec!(("c", 4), ("d", 6), ("e", 3));
        pq.extend(v);
        assert_eq!(pq.len(), 6);
        assert_eq!(pq.into_sorted_vec().as_slice(),
                   &["f", "d", "c", "e", "b", "a"]);
    }

    #[test]
    fn iter() {
        let mut pq = PriorityQueue::new();
        pq.push("a", 1);
        pq.push("b", 2);
        pq.push("f", 7);

        assert_eq!(pq.iter().count(), 3);
    }

    #[test]
    fn into_sorted_iter(){
        let mut pq = PriorityQueue::new();
        pq.push("a", 1);
        pq.push("b", 2);
        pq.push("f", 7);

        assert_eq!(pq.into_sorted_iter().collect::<Vec<_>>(),
                   vec!(("f", 7), ("b", 2), ("a", 1)));
    }

    #[test]
    fn eq(){
        let mut a = PriorityQueue::new();
        let mut b = PriorityQueue::new();
        assert_eq!(a, b);

        a.push("a", 1);
        b.push("a", 1);
        assert_eq!(a, b);

        a.push("b", 2);
        assert_ne!(a, b);

        b.push("f", 7);
        b.push("g", 4);
        b.push("h", 3);
        b.push("b", 2);

        a.push("g", 4);
        a.push("f", 7);
        a.push("h", 3);
        assert_eq!(a, b);
        assert_eq!(b, a);
    }
}

#[cfg(all(feature = "serde", test))]
mod serde_tests_basics{
    extern crate serde_test;
    use self::serde_test::{Token, assert_tokens};
    use ::PriorityQueue;
    #[test]
    fn serde_empty(){
        let pq: PriorityQueue<String, i32> = PriorityQueue::new();
        
        assert_tokens(&pq, &[
            Token::Seq{len: Some(0)},
            Token::SeqEnd
        ]);
    }

    #[test]
    fn serde(){
        let mut pq = PriorityQueue::new();
        
        pq.push("a", 1);
        pq.push("b", 2);
        pq.push("f", 7);
        pq.push("g", 4);
        pq.push("h", 3);

        assert_tokens(&pq, &[
            Token::Seq{len: Some(5)},
            Token::Tuple{len:2},
            Token::BorrowedStr("a"),
            Token::I32(1),
            Token::TupleEnd,

            Token::Tuple{len:2},
            Token::BorrowedStr("b"),
            Token::I32(2),
            Token::TupleEnd,

            Token::Tuple{len:2},
            Token::BorrowedStr("f"),
            Token::I32(7),
            Token::TupleEnd,

            Token::Tuple{len:2},
            Token::BorrowedStr("g"),
            Token::I32(4),
            Token::TupleEnd,

            Token::Tuple{len:2},
            Token::BorrowedStr("h"),
            Token::I32(3),
            Token::TupleEnd,
            Token::SeqEnd
        ]);
    }
}

//more complex tests
//thanks to ckaran
#[cfg(all(feature = "serde", test))]
mod serde_tests_custom_structs{
    extern crate serde_json;
    extern crate uuid;
    extern crate serde;

    use ::PriorityQueue;
    use std::cmp::{Ord, PartialOrd, Ordering};
    use std::default::Default;
    use std::time::Duration;
    use self::uuid::Uuid;

    // Abusing Duration as a mutable std::time::Instant
    type ActivationDate = Duration;

    /// Events are compared by EventComparables instances.
    ///
    /// EventComparables instances are similar to instances of time, but with the
    /// extra wrinkle of having a Uuid instance.  When EventComparables instances
    /// are compared, they are first compared by their activation date, with the
    /// date that occurs earlier being greater than a date that occurs later. This
    /// ordering exists because of how priority_queue::PriorityQueue works; it is
    /// naturally a max priority queue; using this ordering makes it a min
    /// priority queue. EventComparables go one step beyond using time as the key
    /// though; they  also have uuid::Uuid instances which are used to guarantee
    /// that every EventComparables is unique.  This ensures that if a set of
    /// events all  occur at the same time, they will still be executed in a
    /// deterministic order, every single time the queue's contents are executed.
    /// This is  critical for deterministic simulators.
    #[serde(default)]
    #[serde(deny_unknown_fields)]
    #[derive(Copy, Clone, Eq, PartialEq, Hash, Serialize, Deserialize, Debug)]
    struct EventComparables {
        /// This is when the event will be fired.
        activation_date: ActivationDate,

        /// This is a unique ID.  Except for ensuring that different events are
        /// guaranteed to compare as being different, it has no purpose.
        id: Uuid
    }

    /// Default events activate at time (0, 0)
    ///
    /// All default events first at time (0, 0), but every single one has a unique
    /// id.  This ensures that regardless of the number of default events you
    /// create, they will always execute in the same order.
    impl Default for EventComparables {
        fn default() -> Self {
            EventComparables {activation_date: ActivationDate::new(0,0), id: Uuid::new_v4()}
        }
    }

    /// The priority queue depends on `Ord`. Explicitly implement the trait so the
    /// queue becomes a min-heap instead of a max-heap.
    impl Ord for EventComparables {
        fn cmp(&self, other: &Self) -> Ordering {

            // Notice that the we flip the ordering on costs. In case of a tie we
            // compare by id - this step is necessary to make implementations of
            // `PartialEq` and `Ord` consistent.

            other.activation_date.cmp(&self.activation_date)
                .then_with(|| self.id.cmp(&other.id))
        }
    }

    // `PartialOrd` needs to be implemented as well.
    impl PartialOrd for EventComparables {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    /// A fake event to fire on some date.
    ///
    /// This is a fake event that I'll fire when the corresponding
    /// EventComparables instance comes up.  The contents are immaterial; I'm just
    /// using it for testing
    #[serde(default)]
    #[serde(deny_unknown_fields)]
    #[derive(Copy, Clone, Eq, PartialEq, Hash, Serialize, Deserialize, Debug)]
    struct ConcreteEvent1 {
        a: i32,
        b: i64
    }

    impl Default for ConcreteEvent1 {
        fn default() -> Self {
            ConcreteEvent1 {a: 0, b: 0}
        }
    }

    //////////////////////////////////////////////////////////////////////////////
    // Test 1
    //////////////////////////////////////////////////////////////////////////////
    #[test]
    fn test1() {
        println!("test1()");

        type PqType = PriorityQueue<i32, i32>;

        let mut pq: PqType = PriorityQueue::new();
        pq.push(0, 0);
        pq.push(1, 1);

        let serialized = serde_json::to_string(&pq).unwrap();
        println!("serialized = {:?}", serialized);
        let deserialized: PqType = serde_json::from_str(&serialized).unwrap();
        println!("deserialized = {:?}", deserialized);
    }

    //////////////////////////////////////////////////////////////////////////////
    // Test 2
    //////////////////////////////////////////////////////////////////////////////
    #[test]
    fn test2() {
        println!("\n\ntest2()");

        type PqType = PriorityQueue<i32, EventComparables>;

        let mut pq: PqType = PriorityQueue::new();
        pq.push(0, Default::default()); // Uuids will be different
        pq.push(1, Default::default());

        let serialized = serde_json::to_string(&pq).unwrap();
        println!("serialized = {:?}", serialized);
        let deserialized: PqType = serde_json::from_str(&serialized).unwrap();
        println!("deserialized = {:?}", deserialized);
    }

    //////////////////////////////////////////////////////////////////////////////
    // Test 3
    //////////////////////////////////////////////////////////////////////////////
    #[test]
    fn test3() {
        println!("\n\ntest3()");

        // Create some concrete events and comparables, and test to see that they
        // can be serialized/deserialized

        let ce1 = ConcreteEvent1{a: 12, b: 45};
        let ec1 = EventComparables {activation_date: ActivationDate::new(0, 1), id: Uuid::new_v4()};

        let ce2 = ConcreteEvent1{a: 37, b: 123};
        let ec2 = EventComparables {activation_date: ActivationDate::new(0, 1), id: Uuid::new_v4()};

        let serialized = serde_json::to_string(&ce1).unwrap();
        println!("serialized = {:?}", serialized);
        let deserialized: ConcreteEvent1 = serde_json::from_str(&serialized).unwrap();
        println!("deserialized = {:?}", deserialized);
        assert_eq!(ce1, deserialized);

        let serialized = serde_json::to_string(&ec1).unwrap();
        println!("serialized = {:?}", serialized);
        let deserialized: EventComparables = serde_json::from_str(&serialized).unwrap();
        println!("deserialized = {:?}", deserialized);
        assert_eq!(ec1, deserialized);

        let serialized = serde_json::to_string(&ce2).unwrap();
        println!("serialized = {:?}", serialized);
        let deserialized: ConcreteEvent1 = serde_json::from_str(&serialized).unwrap();
        println!("deserialized = {:?}", deserialized);
        assert_eq!(ce2, deserialized);

        let serialized = serde_json::to_string(&ec2).unwrap();
        println!("serialized = {:?}", serialized);
        let deserialized: EventComparables = serde_json::from_str(&serialized).unwrap();
        println!("deserialized = {:?}", deserialized);
        assert_eq!(ec2, deserialized);

        {
            type PqType = PriorityQueue<ConcreteEvent1, EventComparables>;

            let mut pq: PqType = PriorityQueue::new();
            pq.push(ce1, ec1);
            pq.push(ce2, ec2);

            let serialized = serde_json::to_string(&pq).unwrap();
            println!("serialized = {:?}", serialized);
            let deserialized: PqType = serde_json::from_str(&serialized).unwrap();
            println!("deserialized = {:?}", deserialized);
        }
    }
}
