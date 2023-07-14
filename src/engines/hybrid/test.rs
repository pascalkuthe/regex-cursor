use proptest::{prop_assert, prop_assert_eq, proptest};

use crate::engines::hybrid::find_iter;
use crate::input::Input;

#[test]
fn searcher() {
    let text = std::fs::read_to_string("test_cases/syntax.rs").unwrap();
    let regex = super::Regex::builder()
        .syntax(regex_automata::util::syntax::Config::new().case_insensitive(true))
        .build("vec")
        .unwrap();
    let mut cache = regex.create_cache();
    let rope = ropey::Rope::from_str(&text);
    let matches: Vec<_> = super::find_iter(&regex, &mut cache, Input::new(rope.slice(..)))
        .map(|range| rope.byte_slice(range.range()))
        .collect();
    assert_eq!(matches.len(), 68);
}

#[test]
fn anchor() {
    let haystack = ":a";
    let needle = "$|:";
    let foo = ropey::Rope::from_str(&haystack);
    let regex = super::Regex::builder()
        .syntax(regex_automata::util::syntax::Config::new().case_insensitive(true).unicode(false))
        .build(&needle)
        .unwrap();
    let mut cache1 = regex.create_cache();
    let mut cache2 = regex.create_cache();
    let iter1: Vec<_> = regex.find_iter(&mut cache1, &haystack).collect();
    let iter2: Vec<_> = find_iter(&regex, &mut cache2, foo.slice(..)).collect();
    assert_eq!(iter1, iter2);
}

#[test]
fn hotloop_transition() {
    let haystack = "Σ /ⶠaAA ﷏00AAΣ/എ";
    let needle = "/";
    let foo = ropey::Rope::from_str(haystack);
    let regex = super::Regex::builder()
        .syntax(regex_automata::util::syntax::Config::new().case_insensitive(true).unicode(false))
        .build(needle)
        .unwrap();
    let mut cache1 = regex.create_cache();
    let mut cache2 = regex.create_cache();
    let iter1: Vec<_> = regex.find_iter(&mut cache1, haystack).collect();
    let iter2: Vec<_> = find_iter(&regex, &mut cache2, foo.slice(..)).collect();
    assert_eq!(iter1, iter2);
}

proptest! {
  #[test]
  fn matches(haystack: String, needle: String) {
    let foo = ropey::Rope::from_str(&haystack);
    let Ok(regex) = super::Regex::builder()
        .syntax(regex_automata::util::syntax::Config::new()
            .case_insensitive(true)
            .unicode(false),
        )
        .build(&needle) else {
        return Ok(())
    };
    let mut cache1 = regex.create_cache();
    let mut cache2 = regex.create_cache();
    let iter1: Vec<_> = regex.find_iter(&mut cache1, &haystack).collect();
    let iter2: Vec<_> = find_iter(&regex, &mut cache2, foo.slice(..)).collect();
    prop_assert_eq!(iter1, iter2);
  }
}
