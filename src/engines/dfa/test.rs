use proptest::proptest;

use crate::engines::dfa::find_iter;
use crate::input::Input;

#[test]
fn searcher() {
    let text = std::fs::read_to_string("test_cases/syntax.rs").unwrap();
    let regex = super::Regex::builder()
        .syntax(regex_automata::util::syntax::Config::new().case_insensitive(true))
        .build("vec")
        .unwrap();
    let rope = ropey::Rope::from_str(&text);
    let matches: Vec<_> = find_iter(&regex, Input::new(rope.slice(..)))
        .map(|range| rope.byte_slice(range.range()))
        .collect();
    assert_eq!(matches.len(), 68);
}

#[test]
fn anchor() {
    let haystack = ":a";
    let needle = "$|:";
    let foo = ropey::Rope::from_str(haystack);
    let regex = super::Regex::builder()
        .syntax(regex_automata::util::syntax::Config::new().case_insensitive(true).unicode(false))
        .build(needle)
        .unwrap();
    let iter1: Vec<_> = regex.find_iter(haystack).collect();
    let iter2: Vec<_> = find_iter(&regex, Input::new(&foo)).collect();
    assert_eq!(iter1, iter2);
}

#[test]
fn hotloop_transition() {
    let haystack = "Σ /ⶠaAA ﷏00AAΣ/എ";
    let needle = "/";
    let foo = ropey::Rope::from_str(haystack);
    let regex = super::Regex::builder()
        .syntax(regex_automata::util::syntax::Config::new().case_insensitive(true))
        .build(needle)
        .unwrap();
    let iter1: Vec<_> = regex.find_iter(haystack).collect();
    let iter2: Vec<_> = find_iter(&regex, Input::new(&foo)).collect();
    assert_eq!(iter1, iter2);
}

proptest! {
  #[test]
  fn matches(mut haystack: String, needle: String) {
    haystack = haystack.repeat(1024);
    let foo = ropey::Rope::from_str(&haystack);
    let Ok(regex) = super::Regex::builder()
        .syntax(regex_automata::util::syntax::Config::new()
            .case_insensitive(true)
        )
        .build(&needle) else {
        return Ok(())
    };
    let iter1 = regex.find_iter( &haystack);
    let iter2 = find_iter(&regex, Input::new(&foo));
    crate::util::iter::prop_assert_eq(iter1, iter2)?;
  }
}
