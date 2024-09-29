use std::ops::RangeBounds;

use proptest::{prop_assert_eq, proptest};
use regex_automata::nfa::thompson::pikevm::PikeVM;
use regex_automata::nfa::thompson::Config;
use regex_automata::util::escape::DebugHaystack;
use regex_automata::util::syntax::Config as SyntaxConfig;

use crate::engines::pikevm::find_iter;
use crate::input::Input;
use crate::test_rope::SingleByteChunks;

use super::Cache;

fn test(needle: &str, haystack: &[u8]) {
    test_with_bounds(needle, haystack, ..)
}

fn test_with_bounds(needle: &str, haystack: &[u8], bounds: impl RangeBounds<usize> + Clone) {
    for utf8 in [true, false] {
        let regex = PikeVM::builder()
            .syntax(SyntaxConfig::new().utf8(utf8))
            .thompson(Config::new().utf8(utf8))
            .build(needle)
            .unwrap();
        let mut cache1 = regex.create_cache();
        let mut cache2 = Cache::new(&regex);
        let input = regex_automata::Input::new(haystack).range(bounds.clone());
        let iter1: Vec<_> = regex.find_iter(&mut cache1, input).collect();
        let input = Input::new(SingleByteChunks::new(haystack)).range(bounds.clone());
        let iter2: Vec<_> = find_iter(&regex, &mut cache2, input).collect();
        assert_eq!(iter1, iter2, "matches of {needle} in {:?}", DebugHaystack(haystack));
    }
}

#[test]
fn smoke_test() {
    let text = std::fs::read_to_string("test_cases/syntax.rs").unwrap();
    let regex =
        PikeVM::builder().syntax(SyntaxConfig::new().case_insensitive(true)).build("vec").unwrap();
    let mut cache = Cache::new(&regex);
    let rope = ropey::Rope::from_str(&text);
    let matches: Vec<_> = find_iter(&regex, &mut cache, Input::new(&rope))
        .map(|range| rope.byte_slice(range.range()))
        .collect();
    println!("found {matches:#?} in syntax.rs");
    assert_eq!(matches.len(), 68);
}

#[test]
fn any() {
    test(".", b" ");
}

#[test]
fn look_around() {
    test("^bar", b"foobar");
    test("foo$", b"foobar");
    test(r"(?m)(?:^|a)+", b"a\naaa\n");
    test_with_bounds(r"\b{end}", "𝛃".as_bytes(), 2..3);
    let haystack: String =
        (0..5 * 4096).map(|i| format!("foöbar  foÖ{0}bar foö{0}bar", " ".repeat(i % 31))).collect();
    let needle = r"\bfoö\b[ ]*\bbar\b";
    test(needle, haystack.as_bytes())
}

#[test]
fn maybe_empty() {
    test(r"x*", b"x");
    test(r"\bx*\b", b"x");
}

proptest! {
  #[test]
  fn matches(haystack: String, needle: String) {
    let Ok(regex) = PikeVM::builder().syntax(SyntaxConfig::new().case_insensitive(true)).build(&needle) else {
        return Ok(())
    };
    let mut cache1 = regex.create_cache();
    let mut cache2 = Cache::new(&regex);
    let iter1: Vec<_> = regex.find_iter(&mut cache1, &haystack).collect();
    let iter2: Vec<_> = find_iter(&regex, &mut cache2, Input::new(SingleByteChunks::new(haystack.as_bytes()))).collect();
    prop_assert_eq!(iter1, iter2);
  }
  #[test]
  fn matches_word(haystack: String, needle in r"\\b\PC+\\b") {
    let Ok(regex) = PikeVM::builder().syntax(SyntaxConfig::new().case_insensitive(true)).build(&needle) else {
        return Ok(())
    };
    let mut cache1 = regex.create_cache();
    let mut cache2 = Cache::new(&regex);
    let iter1: Vec<_> = regex.find_iter(&mut cache1, &haystack).collect();
    let iter2: Vec<_> = find_iter(&regex, &mut cache2, Input::new(SingleByteChunks::new(haystack.as_bytes()))).collect();
    prop_assert_eq!(iter1, iter2);
  }
}
