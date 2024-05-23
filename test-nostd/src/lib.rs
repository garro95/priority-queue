/*
 *  Copyright 2017 Gianmarco Garrisi and contributors
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
