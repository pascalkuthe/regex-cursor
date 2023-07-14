use std::iter::from_fn;

use proptest::{prop_assert, proptest};
use regex_automata::Span;

proptest! {
    #[test]
    fn matches(haystack: String, needle: [u8; super::ROPEY_MIN_CHUNK_LEN]) {
        let foo = ropey::Rope::from_str(&haystack);
        let Some(filter2) = regex_automata::util::prefilter::Prefilter::new(regex_automata::MatchKind::All, &[&needle]) else {
            return Ok(())
        };
        let filter1 = super::Prefilter::new(regex_automata::MatchKind::All, &[&needle]).unwrap();
        let mut input = crate::Input::new(foo.slice(..));
        let mut span = input.get_span();
        let iter1 = from_fn(||{
            let res = filter1.find(&mut input, span)?;
            span.start = res.end;
            Some(res)
        });
        let mut span = Span{start: 0, end: haystack.len()};
        let iter2 = from_fn(||{
            let res = filter2.find(haystack.as_bytes(), span)?;
            span.start = res.end;
            Some(res)
        });
        prop_assert!(iter1.eq(iter2));
    }
}
