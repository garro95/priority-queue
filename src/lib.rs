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

//! This crate provide a priority queue backed by an hashmap
//! with some efficient methods to change the priority of an element in
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
#![cfg_attr(not(has_std), no_std)]
#![cfg_attr(feature = "benchmarks", feature(test))]

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

#[cfg(all(feature = "serde", test))]
#[macro_use]
extern crate serde_derive;
mod iterators;
mod pqueue;
pub use crate::pqueue::PriorityQueue;

#[cfg(test)]
mod tests {
    pub use crate::PriorityQueue;

    #[test]
    fn init() {
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
    fn push_increase() {
        let mut pq = PriorityQueue::new();
        pq.push("Processor", 1);
        pq.push("Mainboard", 2);
        pq.push("RAM", 5);
        pq.push("GPU", 4);
        pq.push("Disk", 3);

        let processor_priority = |pq: &PriorityQueue<&str, i32>| {
            *pq.iter()
                .filter_map(|(i, p)| if *i == "Processor" { Some(p) } else { None })
                .next()
                .unwrap()
        };

        pq.push_increase("Processor", 3);
        assert_eq!(processor_priority(&pq), 3);

        pq.push_increase("Processor", 1);
        assert_eq!(processor_priority(&pq), 3);

        pq.push_increase("Processor", 6);
        assert_eq!(pq.peek(), Some((&"Processor", &6)));
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
    fn change_priority_does_not_change_contents() {
        use std::hash::{Hash, Hasher};
        struct MyFn {
            name: &'static str,
            func: fn(&mut i32),
        }
        impl Default for MyFn {
            fn default() -> Self {
                Self {
                    name: "",
                    func: |_| {},
                }
            }
        }
        impl PartialEq for MyFn {
            fn eq(&self, other: &Self) -> bool {
                self.name == other.name
            }
        }
        impl Eq for MyFn {}
        impl Hash for MyFn {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.name.hash(state);
            }
        }
        impl std::fmt::Debug for MyFn {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write![f, "{:?}", self.name]
            }
        }

        let mut pq = PriorityQueue::new();
        pq.push(
            MyFn {
                name: "increment-one",
                func: |x| *x += 1,
            },
            2,
        );
        pq.push(
            MyFn {
                name: "increment-two",
                func: |x| *x += 2,
            },
            1,
        );

        let mut cnt = 0;
        assert_eq![
            pq.peek(),
            Some((
                &MyFn {
                    name: "increment-one",
                    func: |_| {}
                },
                &2
            ))
        ];
        pq.change_priority(
            &MyFn {
                name: "increment-one",
                func: |_| {},
            },
            0,
        );
        assert_eq![
            pq.peek(),
            Some((
                &MyFn {
                    name: "increment-two",
                    func: |_| {}
                },
                &1
            ))
        ];

        assert_eq![cnt, 0];

        (pq.pop().unwrap().0.func)(&mut cnt);
        assert_eq![cnt, 2];

        (pq.pop().unwrap().0.func)(&mut cnt);
        assert_eq![cnt, 3];
    }

    #[test]
    fn reversed_order() {
        use std::cmp::Reverse;
        let mut pq: PriorityQueue<_, Reverse<i32>> = PriorityQueue::new();
        pq.push("a", Reverse(1));
        pq.push("b", Reverse(2));
        assert_eq![pq.pop(), Some(("a", Reverse(1)))];
    }

    #[test]
    fn from_vec() {
        let v = vec![("a", 1), ("b", 2), ("f", 7)];
        let mut pq: PriorityQueue<_, _> = PriorityQueue::from(v);
        assert_eq!(pq.pop(), Some(("f", 7)));
        assert_eq!(pq.len(), 2);
    }

    #[test]
    fn from_vec_with_repeated() {
        let v = vec![("a", 1), ("b", 2), ("f", 7), ("a", 2)];
        let mut pq: PriorityQueue<_, _> = v.into();
        assert_eq!(pq.pop(), Some(("f", 7)));
        assert_eq!(pq.len(), 2);
    }

    #[test]
    fn from_iter() {
        use std::iter::FromIterator;

        let v = vec![("a", 1), ("b", 2), ("f", 7)];
        let mut pq: PriorityQueue<_, _> = PriorityQueue::from_iter(v.into_iter());
        assert_eq!(pq.pop(), Some(("f", 7)));
        assert_eq!(pq.len(), 2);
    }

    #[test]
    fn heap_sort() {
        type Pq<I, P> = PriorityQueue<I, P>;

        let v = vec![("a", 2), ("b", 7), ("f", 1)];
        let sorted = (Pq::from(v)).into_sorted_vec();
        assert_eq!(sorted.as_slice(), &["b", "a", "f"]);
    }

    #[test]
    fn change_priority_by() {
        use std::iter::FromIterator;

        let v = vec![("a", 1), ("b", 2), ("f", 7), ("g", 6), ("h", 5)];
        let mut pq: PriorityQueue<_, _> = PriorityQueue::from_iter(v.into_iter());

        pq.change_priority_by("b", |b| *b += 8);
        assert_eq!(pq.into_sorted_vec().as_slice(), &["b", "f", "g", "h", "a"]);
    }

    #[test]
    fn remove_empty() {
        let mut pq: PriorityQueue<&str, i32> = PriorityQueue::new();

        pq.remove(&"b");
        assert_eq!(pq.len(), 0);
    }

    #[test]
    fn remove_one() {
        let mut pq = PriorityQueue::new();

        pq.push("b", 21);

        assert_eq!(Some(("b", 21)), pq.remove(&"b"));
        assert_eq!(pq.len(), 0);
    }

    #[test]
    fn remove() {
        use std::iter::FromIterator;
        type Pq<I, P> = PriorityQueue<I, P>;

        let v = vec![("a", 1), ("b", 2), ("f", 7), ("g", 6), ("h", 5)];
        let mut pq = Pq::from_iter(v.into_iter());

        pq.remove(&"b").unwrap();
        pq.push("b", 2);
        pq.remove(&"b");
        assert_eq!(["f", "g", "h", "a"], pq.into_sorted_vec().as_slice());
    }

    #[test]
    fn remove2() {
	use std::collections::hash_map::RandomState;
	let mut queue = PriorityQueue::<i32, i32, RandomState>::default();

	for i in 0..7 {
            queue.push(i, i);
	}

	queue.remove(&0);

	let mut last_priority = *queue.peek().unwrap().1;
	while let Some((_, priority)) = queue.pop() {
            dbg!(priority);
            assert!(last_priority >= priority);
            last_priority = priority;
	}
    }

    #[test]
    fn extend() {
        let mut pq = PriorityQueue::new();
        pq.push("a", 1);
        pq.push("b", 2);
        pq.push("f", 7);

        let v = vec![("c", 4), ("d", 6), ("e", 3)];
        pq.extend(v);
        assert_eq!(pq.len(), 6);
        assert_eq!(
            pq.into_sorted_vec().as_slice(),
            &["f", "d", "c", "e", "b", "a"]
        );
    }

    #[test]
    fn extend_empty() {
        let mut pq = PriorityQueue::new();

        let v = vec![("c", 4), ("d", 6), ("e", 3)];
        pq.extend(v);
        assert_eq!(pq.len(), 3);
        assert_eq!(pq.into_sorted_vec().as_slice(), &["d", "c", "e"]);
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
    fn iter_mut() {
        let mut pq = PriorityQueue::new();
        pq.push("a", 1);
        pq.push("b", 2);
        pq.push("f", 7);
        pq.push("g", 4);
        pq.push("h", 3);

        for (i, p) in &mut pq {
            if *i < "f" {
                *p += 18;
            }
        }

        assert_eq!(pq.pop(), Some(("b", 20)));

        /*
        As expected, this does not compile
        let iter_mut = pq.iter_mut();
        iter_mut.for_each(|(_, p)| {*p += 2});

        assert_eq!(pq.pop(), Some(("f", 9)));
        */
    }

    #[test]
    fn into_sorted_iter() {
        let mut pq = PriorityQueue::new();
        pq.push("a", 1);
        pq.push("b", 2);
        pq.push("f", 7);

        assert_eq!(
            pq.into_sorted_iter().collect::<Vec<_>>(),
            vec!(("f", 7), ("b", 2), ("a", 1))
        );
    }

    #[test]
    fn iter_mut1() {
        let mut queue: PriorityQueue<&'static str, i32> = Default::default();

        queue.push("a", 0);
        queue.push("b", 1);
        assert_eq!(queue.peek().unwrap().0, &"b");

	let iter_mut = queue.iter_mut();
        for (k, v) in iter_mut {
	    if k == &"a" {
                *v = 2;
	    }
        }

        assert_eq!(queue.peek().unwrap().0, &"a");
    }

    #[test]
    fn iter_mut_empty() {
        let mut queue: PriorityQueue<&'static str, i32> = Default::default();

	let iter_mut = queue.iter_mut();
        for (k, v) in iter_mut {
	    if k == &"a" {
                *v = 2;
	    }
        }
    }

    #[test]
    fn eq() {
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

    #[test]
    fn non_default_key() {
        use std::time::*;
        type PqType = PriorityQueue<i32, Instant>;
        let _: PqType = PriorityQueue::default();
    }
}

#[cfg(all(feature = "serde", test))]
mod serde_tests_basics {
    use crate::PriorityQueue;
    use serde_test::{assert_tokens, Token};
    #[test]
    fn serde_empty() {
        let pq: PriorityQueue<String, i32> = PriorityQueue::new();

        assert_tokens(&pq, &[Token::Seq { len: Some(0) }, Token::SeqEnd]);
    }

    #[test]
    fn serde() {
        let mut pq = PriorityQueue::new();

        pq.push("a", 1);
        pq.push("b", 2);
        pq.push("f", 7);
        pq.push("g", 4);
        pq.push("h", 3);

        assert_tokens(
            &pq,
            &[
                Token::Seq { len: Some(5) },
                Token::Tuple { len: 2 },
                Token::BorrowedStr("a"),
                Token::I32(1),
                Token::TupleEnd,
                Token::Tuple { len: 2 },
                Token::BorrowedStr("b"),
                Token::I32(2),
                Token::TupleEnd,
                Token::Tuple { len: 2 },
                Token::BorrowedStr("f"),
                Token::I32(7),
                Token::TupleEnd,
                Token::Tuple { len: 2 },
                Token::BorrowedStr("g"),
                Token::I32(4),
                Token::TupleEnd,
                Token::Tuple { len: 2 },
                Token::BorrowedStr("h"),
                Token::I32(3),
                Token::TupleEnd,
                Token::SeqEnd,
            ],
        );
    }
}

//more complex tests
//thanks to ckaran
#[cfg(all(feature = "serde", test))]
mod serde_tests_custom_structs {
    use crate::PriorityQueue;
    use std::cmp::{Ord, Ordering, PartialOrd};
    use std::default::Default;
    use std::time::Duration;
    use uuid::Uuid;

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
        id: Uuid,
    }

    /// Default events activate at time (0, 0)
    ///
    /// All default events first at time (0, 0), but every single one has a unique
    /// id.  This ensures that regardless of the number of default events you
    /// create, they will always execute in the same order.
    impl Default for EventComparables {
        fn default() -> Self {
            EventComparables {
                activation_date: ActivationDate::new(0, 0),
                id: Uuid::new_v4(),
            }
        }
    }

    /// The priority queue depends on `Ord`. Explicitly implement the trait so the
    /// queue becomes a min-heap instead of a max-heap.
    impl Ord for EventComparables {
        fn cmp(&self, other: &Self) -> Ordering {
            // Notice that the we flip the ordering on costs. In case of a tie we
            // compare by id - this step is necessary to make implementations of
            // `PartialEq` and `Ord` consistent.

            other
                .activation_date
                .cmp(&self.activation_date)
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
        b: i64,
    }

    impl Default for ConcreteEvent1 {
        fn default() -> Self {
            ConcreteEvent1 { a: 0, b: 0 }
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

        let ce1 = ConcreteEvent1 { a: 12, b: 45 };
        let ec1 = EventComparables {
            activation_date: ActivationDate::new(0, 1),
            id: Uuid::new_v4(),
        };

        let ce2 = ConcreteEvent1 { a: 37, b: 123 };
        let ec2 = EventComparables {
            activation_date: ActivationDate::new(0, 1),
            id: Uuid::new_v4(),
        };

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

#[cfg(all(test, feature = "benchmarks"))]
mod benchmarks {
    extern crate test;
    use crate::PriorityQueue;
    use hashbrown::hash_map::DefaultHashBuilder;
    use test::{black_box, Bencher};

    #[bench]
    fn push_and_pop(b: &mut Bencher) {
        type PqType = PriorityQueue<usize, i32>;
        let mut pq: PqType = PriorityQueue::new();
        b.iter(|| {
            pq.push(black_box(0), black_box(0));
            assert_eq![pq.pop().unwrap().1, 0];
        });
    }

    #[bench]
    fn push_and_pop_fx(b: &mut Bencher) {
        let mut pq = PriorityQueue::<_, _, DefaultHashBuilder>::with_default_hasher();
        b.iter(|| {
            pq.push(black_box(0), black_box(0));
            assert_eq![pq.pop().unwrap().1, 0];
        });
    }

    //for comparison, using the BinaryHeap
    #[bench]
    fn push_and_pop_std(b: &mut Bencher) {
        use std::collections::BinaryHeap;
        type PqType = BinaryHeap<(usize, i32)>;
        let mut pq: PqType = BinaryHeap::new();
        b.iter(|| {
            pq.push((black_box(0), black_box(0)));
            assert_eq![pq.pop().unwrap().1, 0];
        });
    }

    #[bench]
    fn push_and_pop_on_large_queue(b: &mut Bencher) {
        type PqType = PriorityQueue<usize, i32>;
        let mut pq: PqType = PriorityQueue::new();
        for i in 0..100_000 {
            pq.push(black_box(i as usize), black_box(i));
        }
        b.iter(|| {
            pq.push(black_box(100_000), black_box(100_000));
            assert_eq![pq.pop().unwrap().1, black_box(100_000)];
        });
    }
    #[bench]
    fn push_and_pop_on_large_queue_fx(b: &mut Bencher) {
        let mut pq = PriorityQueue::<_, _, DefaultHashBuilder>::with_default_hasher();
        for i in 0..100_000 {
            pq.push(black_box(i as usize), black_box(i));
        }
        b.iter(|| {
            pq.push(black_box(100_000), black_box(100_000));
            assert_eq![pq.pop().unwrap().1, black_box(100_000)];
        });
    }

    #[bench]
    fn push_and_pop_on_large_queue_std(b: &mut Bencher) {
        use std::collections::BinaryHeap;
        type PqType = BinaryHeap<(usize, i32)>;
        let mut pq: PqType = BinaryHeap::new();
        for i in 0..100_000 {
            pq.push((black_box(i as usize), black_box(i)));
        }
        b.iter(|| {
            pq.push((black_box(100_000), black_box(100_000)));
            assert_eq![pq.pop().unwrap().1, black_box(100_000)];
        });
    }

    #[bench]
    fn priority_change_on_large_queue_std(b: &mut Bencher) {
        use std::collections::BinaryHeap;
        struct Entry(usize, i32);
        impl Ord for Entry {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.0.cmp(&other.0)
            }
        }
        impl PartialOrd for Entry {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                self.0.partial_cmp(&other.0)
            }
        }
        impl Eq for Entry {}
        impl PartialEq for Entry {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }
        type PqType = BinaryHeap<Entry>;
        let mut pq: PqType = BinaryHeap::new();
        for i in 0..100_000 {
            pq.push(Entry(black_box(i as usize), black_box(i)));
        }
        b.iter(|| {
            pq = pq
                .drain()
                .map(|Entry(i, p)| {
                    if i == 50_000 {
                        Entry(i, p / 2)
                    } else {
                        Entry(i, p)
                    }
                })
                .collect()
        });
    }

    #[bench]
    fn priority_change_on_large_queue(b: &mut Bencher) {
        type PqType = PriorityQueue<usize, i32>;
        let mut pq: PqType = PriorityQueue::new();
        for i in 0..100_000 {
            pq.push(black_box(i as usize), black_box(i));
        }
        b.iter(|| {
            pq.change_priority_by(&50_000, |p| *p = *p / 2);
        });
    }
    #[bench]
    fn priority_change_on_large_queue_fx(b: &mut Bencher) {
        let mut pq = PriorityQueue::<_, _, DefaultHashBuilder>::with_default_hasher();
        for i in 0..100_000 {
            pq.push(black_box(i as usize), black_box(i));
        }
        b.iter(|| {
            pq.change_priority_by(&50_000, |p| *p = *p / 2);
        });
    }

    #[bench]
    fn priority_change_on_small_queue_std(b: &mut Bencher) {
        use std::collections::BinaryHeap;
        struct Entry(usize, i32);
        impl Ord for Entry {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.0.cmp(&other.0)
            }
        }
        impl PartialOrd for Entry {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                self.0.partial_cmp(&other.0)
            }
        }
        impl Eq for Entry {}
        impl PartialEq for Entry {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }
        type PqType = BinaryHeap<Entry>;
        let mut pq: PqType = BinaryHeap::new();
        for i in 0..1_000 {
            pq.push(Entry(black_box(i as usize), black_box(i)));
        }
        b.iter(|| {
            pq = pq
                .drain()
                .map(|Entry(i, p)| {
                    if i == 500 {
                        Entry(i, p / 2)
                    } else {
                        Entry(i, p)
                    }
                })
                .collect()
        });
    }

    #[bench]
    fn priority_change_on_small_queue(b: &mut Bencher) {
        type PqType = PriorityQueue<usize, i32>;
        let mut pq: PqType = PriorityQueue::new();
        for i in 0..1_000 {
            pq.push(black_box(i as usize), black_box(i));
        }
        b.iter(|| {
            pq.change_priority_by(&500, |p| *p = *p / 2);
        });
    }
    #[bench]
    fn priority_change_on_small_queue_fx(b: &mut Bencher) {
        let mut pq = PriorityQueue::<_, _, DefaultHashBuilder>::with_default_hasher();
        for i in 0..1_000 {
            pq.push(black_box(i as usize), black_box(i));
        }
        b.iter(|| {
            pq.change_priority_by(&500, |p| *p = *p / 2);
        });
    }
}
