/*!
This module defines a sparse set data structure. Its most interesting
properties are:

* They preserve insertion order.
* Set membership testing is done in constant time.
* Set insertion is done in constant time.
* Clearing the set is done in constant time.

The cost for doing this is that the capacity of the set needs to be known up
front, and the elements in the set are limited to state identifiers.

These sets are principally used when traversing an NFA state graph. This
happens at search time, for example, in the PikeVM. It also happens during DFA
determinization.
*/

use std::vec;
use std::vec::Vec;

use regex_automata::util::primitives::StateID;

/// A sparse set used for representing ordered NFA states.
///
/// This supports constant time addition and membership testing. Clearing an
/// entire set can also be done in constant time. Iteration yields elements
/// in the order in which they were inserted.
///
/// The data structure is based on: https://research.swtch.com/sparse
/// Note though that we don't actually use uninitialized memory. We generally
/// reuse sparse sets, so the initial allocation cost is bareable. However, its
/// other properties listed above are extremely useful.
#[derive(Clone)]
pub(crate) struct SparseSet {
    /// The number of elements currently in this set.
    len: usize,
    /// Dense contains the ids in the order in which they were inserted.
    dense: Vec<StateID>,
    /// Sparse maps ids to their location in dense.
    ///
    /// A state ID is in the set if and only if
    /// sparse[id] < len && id == dense[sparse[id]].
    ///
    /// Note that these are indices into 'dense'. It's a little weird to use
    /// StateID here, but we know our length can never exceed the bounds of
    /// StateID (enforced by 'resize') and StateID will be at most 4 bytes
    /// where as a usize is likely double that in most cases.
    sparse: Vec<StateID>,
}

impl SparseSet {
    /// Create a new sparse set with the given capacity.
    ///
    /// Sparse sets have a fixed size and they cannot grow. Attempting to
    /// insert more distinct elements than the total capacity of the set will
    /// result in a panic.
    ///
    /// This panics if the capacity given is bigger than `StateID::LIMIT`.
    #[inline]
    pub(crate) fn new(capacity: usize) -> SparseSet {
        let mut set = SparseSet { len: 0, dense: vec![], sparse: vec![] };
        set.resize(capacity);
        set
    }

    /// Resizes this sparse set to have the new capacity given.
    ///
    /// This set is automatically cleared.
    ///
    /// This panics if the capacity given is bigger than `StateID::LIMIT`.
    #[inline]
    pub(crate) fn resize(&mut self, new_capacity: usize) {
        assert!(
            new_capacity <= StateID::LIMIT,
            "sparse set capacity cannot excced {:?}",
            StateID::LIMIT
        );
        self.clear();
        self.dense.resize(new_capacity, StateID::ZERO);
        self.sparse.resize(new_capacity, StateID::ZERO);
    }

    /// Returns the capacity of this set.
    ///
    /// The capacity represents a fixed limit on the number of distinct
    /// elements that are allowed in this set. The capacity cannot be changed.
    #[inline]
    pub(crate) fn capacity(&self) -> usize {
        self.dense.len()
    }

    /// Returns the number of elements in this set.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    /// Returns true if and only if this set is empty.
    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Insert the state ID value into this set and return true if the given
    /// state ID was not previously in this set.
    ///
    /// This operation is idempotent. If the given value is already in this
    /// set, then this is a no-op.
    ///
    /// If more than `capacity` ids are inserted, then this panics.
    ///
    /// This is marked as inline(always) since the compiler won't inline it
    /// otherwise, and it's a fairly hot piece of code in DFA determinization.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn insert(&mut self, id: StateID) -> bool {
        if self.contains(id) {
            return false;
        }

        let i = self.len();
        assert!(
            i < self.capacity(),
            "{:?} exceeds capacity of {:?} when inserting {:?}",
            i,
            self.capacity(),
            id,
        );
        // OK since i < self.capacity() and self.capacity() is guaranteed to
        // be <= StateID::LIMIT.
        let index = StateID::new_unchecked(i);
        self.dense[index] = id;
        self.sparse[id] = index;
        self.len += 1;
        true
    }

    /// Returns true if and only if this set contains the given value.
    #[inline]
    pub(crate) fn contains(&self, id: StateID) -> bool {
        let index = self.sparse[id];
        index.as_usize() < self.len() && self.dense[index] == id
    }

    /// Clear this set such that it has no members.
    #[inline]
    pub(crate) fn clear(&mut self) {
        self.len = 0;
    }

    #[inline]
    pub(crate) fn iter(&self) -> SparseSetIter<'_> {
        SparseSetIter(self.dense[..self.len()].iter())
    }

    /// Returns the heap memory usage, in bytes, used by this sparse set.
    #[inline]
    pub(crate) fn memory_usage(&self) -> usize {
        self.dense.len() * StateID::SIZE + self.sparse.len() * StateID::SIZE
    }
}

impl core::fmt::Debug for SparseSet {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let elements: Vec<StateID> = self.iter().collect();
        f.debug_tuple("SparseSet").field(&elements).finish()
    }
}

/// An iterator over all elements in a sparse set.
///
/// The lifetime `'a` refers to the lifetime of the set being iterated over.
#[derive(Debug)]
pub(crate) struct SparseSetIter<'a>(core::slice::Iter<'a, StateID>);

impl<'a> Iterator for SparseSetIter<'a> {
    type Item = StateID;

    #[cfg_attr(feature = "perf-inline", inline(always))]
    fn next(&mut self) -> Option<StateID> {
        self.0.next().copied()
    }
}
