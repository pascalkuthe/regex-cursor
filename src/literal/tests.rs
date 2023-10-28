use std::iter::from_fn;

use proptest::{prop_assert, proptest};
use regex_automata::util::prefilter::Prefilter;
use regex_automata::Span;

proptest! {
    #[test]
    fn matches(mut haystack: String, needle: String) {
        haystack = haystack.repeat(1024);
        let needles = &[needle.as_bytes()];
        let Some(prefilter) = Prefilter::new(regex_automata::MatchKind::All, needles) else {
            return Ok(())
        };
        let mut span = Span{ start: 0, end: haystack.len() };
        let iter1 = from_fn(||{
            let res = prefilter.find(haystack.as_bytes(), span)?;
            span.start = res.end;
            Some(res)
        });
        let rope = ropey::Rope::from_str(&haystack);
        let mut input = crate::Input::new(rope.chunks());
        let iter2 = from_fn(||{
            let res = super::find(&prefilter, &mut input)?;
            input.set_range(res.end..);
            Some(res)
        });
        prop_assert!(iter1.eq(iter2));
    }
}
