use std::iter;

use proptest::{prop_assert_eq, proptest};
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
        let iter1: Vec<_> = iter::from_fn(||{
            let res = prefilter.find(haystack.as_bytes(), span)?;
            span.start = res.end;
            Some(res)
        }).collect();
        let rope = ropey::Rope::from_str(&haystack);
        let mut input = crate::Input::new(&rope);
        let iter2: Vec<_> = iter::from_fn(||{
            let res = super::find(&prefilter, &mut input)?;
            input.move_to(res.end);
            Some(res)
        }).collect();
        prop_assert_eq!(iter1, iter2);
    }
}
