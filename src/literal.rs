use regex_automata::util::prefilter::Prefilter as Impl;
pub use regex_automata::MatchKind;

pub struct Prefilter {
    inner: Impl,
    max_needle_len: usize,
}

impl Prefilter {
    pub fn new<B: AsRef<[u8]>>(kind: MatchKind, needles: &[B]) -> Option<Prefilter> {
        Impl::new(kind, needles).map(|inner| Prefilter {
            inner,
            max_needle_len: needles
                .iter()
                .map(|needle| needle.as_ref().len())
                .max()
                .expect("atleast one needle required for construction prefilter"),
        })
    }

    // fn find(&self, haystack: &[u8], span: Span) -> Option<Span> {
    //     (&**self).find(haystack, span)
    // }

    // fn prefix(&self, haystack: &[u8], span: Span) -> Option<Span> {
    //     self.inner.prefix(haystack, span)
    // }

    fn memory_usage(&self) -> usize {
        self.inner.memory_usage()
    }

    // fn is_fast(&self) -> bool {
    //     self.inner.is_fast()
    // }
}

// fn search()
