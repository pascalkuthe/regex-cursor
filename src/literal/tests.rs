use std::iter;

use proptest::proptest;
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
        let iter1 = iter::from_fn(||{
            let res = prefilter.find(haystack.as_bytes(), span)?;
            span.start = res.end;
            Some(res)
        });
        let rope = ropey::Rope::from_str(&haystack);
        let mut input = crate::Input::new(&rope);
        let iter2= iter::from_fn(||{
            let res = super::find(&prefilter, &mut input)?;
            input.move_to(res.end);
            Some(res)
        });
        crate::util::iter::prop_assert_eq(iter1, iter2)?;
    }

    #[test]
    fn matches_range(mut haystack: String, needle: String) {
        haystack = haystack.repeat(1024);
        let start = haystack.len() / 3;
        let end = 2*start;
        let needles = &[needle.as_bytes()];
        let Some(prefilter) = Prefilter::new(regex_automata::MatchKind::All, needles) else {
            return Ok(())
        };
        let mut span = Span{ start, end };
        let iter1 = iter::from_fn(||{
            let res = prefilter.find(haystack.as_bytes(), span)?;
            span.start = res.end;
            Some(res)
        });
        let rope = ropey::Rope::from_str(&haystack);
        let mut input = crate::Input::new(&rope).range(start..end);
        let iter2 = iter::from_fn(||{
            let res = super::find(&prefilter, &mut input)?;
            assert!(res.end <= end);
            input.move_to(res.end);
            Some(res)
        });
        crate::util::iter::prop_assert_eq(iter1, iter2)?;
    }
}
