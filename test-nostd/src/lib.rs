#![no_std]

use core::hash::BuildHasherDefault;
use priority_queue::PriorityQueue;
use twox_hash::XxHash64;

use core::iter::FromIterator;

type PQ<P, I> = PriorityQueue<P, I, BuildHasherDefault<XxHash64>>;

pub fn test_compile() {
    let mut queue = PQ::default();
    queue.push(1, 1);
    queue.push(2, 4);
    for (_, _) in queue.iter() {}

    let _queue2 = PQ::from_iter(Some((1, 1)));
}
