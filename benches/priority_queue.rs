#![cfg_attr(feature = "benchmarks", feature(test))]

#[cfg(all(test, feature = "benchmarks"))]
mod benchmarks {
    extern crate test;
    use priority_queue::PriorityQueue;
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
