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
use std::iter::*;

use ::pqueue::PriorityQueue;

pub struct Iter<'a, I:'a, P:'a> {
    pub(crate) iter: ::indexmap::map::Iter<'a, I, Option<P>>
}

impl<'a, I: 'a, P: 'a> Iterator for Iter<'a, I, P> 
    where I: Hash + Eq,
          P: Ord {
    type Item = (&'a I, &'a P);
    fn next(&mut self) -> Option<(&'a I, &'a P)> {
        self.iter.next().map(|(i, op)| (i, op.as_ref().unwrap()))
    }
}

pub struct IntoIter<I,P>
    where I:Hash + Eq,
          P:Ord{
    pub(crate) iter: ::indexmap::map::IntoIter<I, Option<P>>
}

impl<I, P> Iterator for IntoIter<I, P>
    where I:Hash + Eq,
          P:Ord {
    type Item = (I, P);
    fn next(&mut self) -> Option<(I, P)> {
        self.iter.next().map(|(i, op)| (i, op.unwrap()))
    }
}

pub struct IntoSortedIter<I, P>
    where I:Hash + Eq,
          P:Ord {
    pub(crate) pq: PriorityQueue<I, P>
}

impl<I, P> Iterator for IntoSortedIter<I, P>
    where I: Hash + Eq,
          P:Ord {
    type Item = (I, P);
    fn next(&mut self) -> Option<(I, P)> {
        self.pq.pop()
    }
}
