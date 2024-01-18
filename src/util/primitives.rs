use regex_automata::util::primitives::SmallIndex;
use regex_automata::PatternID;

#[derive(Clone, Debug)]
pub(crate) struct SmallIndexIter {
    rng: core::ops::Range<usize>,
}

impl Iterator for SmallIndexIter {
    type Item = SmallIndex;

    fn next(&mut self) -> Option<SmallIndex> {
        if self.rng.start >= self.rng.end {
            return None;
        }
        let next_id = self.rng.start + 1;
        let id = core::mem::replace(&mut self.rng.start, next_id);
        // new_unchecked is OK since we asserted that the number of
        // elements in this iterator will fit in an ID at construction.
        Some(SmallIndex::new_unchecked(id))
    }
}

macro_rules! index_type_impls {
    ($name:ident, $err:ident, $iter:ident, $withiter:ident) => {
        #[derive(Clone, Debug)]
        pub(crate) struct $iter(SmallIndexIter);

        impl $iter {
            fn new(len: usize) -> $iter {
                assert!(
                    len <= $name::LIMIT,
                    "cannot create iterator for {} when number of \
                     elements exceed {:?}",
                    stringify!($name),
                    $name::LIMIT,
                );
                $iter(SmallIndexIter { rng: 0..len })
            }
        }

        impl Iterator for $iter {
            type Item = $name;

            fn next(&mut self) -> Option<$name> {
                self.0.next().map(|id| $name::new_unchecked(id.as_usize()))
            }
        }

        /// An iterator adapter that is like std::iter::Enumerate, but attaches
        /// small index values instead. It requires `ExactSizeIterator`. At
        /// construction, it ensures that the index of each element in the
        /// iterator is representable in the corresponding small index type.
        #[derive(Clone, Debug)]
        pub(crate) struct $withiter<I> {
            it: I,
            ids: $iter,
        }

        impl<I: Iterator + ExactSizeIterator> $withiter<I> {
            fn new(it: I) -> $withiter<I> {
                let ids = $iter::new(it.len());
                $withiter { it, ids }
            }
        }

        impl<I: Iterator + ExactSizeIterator> Iterator for $withiter<I> {
            type Item = ($name, I::Item);

            fn next(&mut self) -> Option<($name, I::Item)> {
                let item = self.it.next()?;
                // Number of elements in this iterator must match, according
                // to contract of ExactSizeIterator.
                let id = self.ids.next().unwrap();
                Some((id, item))
            }
        }
    };
}

index_type_impls!(PatternID, PatternIDError, PatternIDIter, WithPatternIDIter);
// index_type_impls!(StateID, StateIDError, StateIDIter, WithStateIDIter);

/// A utility trait that defines a couple of adapters for making it convenient
/// to access indices as "small index" types. We require ExactSizeIterator so
/// that iterator construction can do a single check to make sure the index of
/// each element is representable by its small index type.
pub(crate) trait IteratorIndexExt: Iterator {
    fn with_pattern_ids(self) -> WithPatternIDIter<Self>
    where
        Self: Sized + ExactSizeIterator,
    {
        WithPatternIDIter::new(self)
    }

    // fn with_state_ids(self) -> WithStateIDIter<Self>
    // where
    //     Self: Sized + ExactSizeIterator,
    // {
    //     WithStateIDIter::new(self)
    // }
}

impl<I: Iterator> IteratorIndexExt for I {}
