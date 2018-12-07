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

use std::cmp::{Eq, Ord};
use std::hash::Hash;
use std::iter::*;

use crate::pqueue::PriorityQueue;

pub struct Iter<'a, I: 'a, P: 'a>
where
    I: Hash + Eq,
    P: Ord,
{
    pub(crate) iter: ::indexmap::map::Iter<'a, I, Option<P>>,
}

impl<'a, I: 'a, P: 'a> Iterator for Iter<'a, I, P>
where
    I: Hash + Eq,
    P: Ord,
{
    type Item = (&'a I, &'a P);
    fn next(&mut self) -> Option<(&'a I, &'a P)> {
        self.iter.next().map(|(i, op)| (i, op.as_ref().unwrap()))
    }
}

pub struct IterMut<'a, I: 'a, P: 'a>
where
    I: Hash + Eq,
    P: Ord,
{
    pq: &'a mut PriorityQueue<I, P>,
    pos: usize,
}

impl<'a, I: 'a, P: 'a> IterMut<'a, I, P>
where
    I: Hash + Eq,
    P: Ord,
{
    pub(crate) fn new(pq: &'a mut PriorityQueue<I, P>) -> Self {
        IterMut { pq, pos: 0 }
    }
}

impl<'a, 'b: 'a, I: 'a, P: 'a> Iterator for IterMut<'a, I, P>
where
    I: Hash + Eq,
    P: Ord,
{
    type Item = (&'a mut I, &'a mut P);
    fn next(&mut self) -> Option<Self::Item> {
        let r: Option<(&'a mut I, &'a mut P)> = self
            .pq
            .map
            .get_index_mut(self.pos)
            .map(|(i, op)| (i, op.as_mut().unwrap()))
            .map(|(i, p)| (i as *mut I, p as *mut P))
            .map(|(i, p)| unsafe { (i.as_mut().unwrap(), p.as_mut().unwrap()) });
        self.pos += 1;
        r
    }
}

impl<'a, I: 'a, P: 'a> Drop for IterMut<'a, I, P>
where
    I: Hash + Eq,
    P: Ord,
{
    fn drop(&mut self) {
        self.pq.heap_build();
    }
}

pub struct IntoIter<I, P>
where
    I: Hash + Eq,
    P: Ord,
{
    pub(crate) iter: ::indexmap::map::IntoIter<I, Option<P>>,
}

impl<I, P> Iterator for IntoIter<I, P>
where
    I: Hash + Eq,
    P: Ord,
{
    type Item = (I, P);
    fn next(&mut self) -> Option<(I, P)> {
        self.iter.next().map(|(i, op)| (i, op.unwrap()))
    }
}

pub struct IntoSortedIter<I, P>
where
    I: Hash + Eq,
    P: Ord,
{
    pub(crate) pq: PriorityQueue<I, P>,
}

impl<I, P> Iterator for IntoSortedIter<I, P>
where
    I: Hash + Eq,
    P: Ord,
{
    type Item = (I, P);
    fn next(&mut self) -> Option<(I, P)> {
        self.pq.pop()
    }
}
