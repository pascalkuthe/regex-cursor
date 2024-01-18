use proptest::{prop_assert_eq, proptest};
use regex_automata::nfa::thompson::pikevm::PikeVM;
use regex_automata::util::syntax::Config;

use crate::engines::pikevm::find_iter;
use crate::input::Input;

use super::Cache;

#[test]
fn smoke_test() {
    let text = std::fs::read_to_string("test_cases/syntax.rs").unwrap();
    let regex =
        PikeVM::builder().syntax(Config::new().case_insensitive(true)).build("vec").unwrap();
    let mut cache = Cache::new(&regex);
    let rope = ropey::Rope::from_str(&text);
    let matches: Vec<_> = find_iter(&regex, &mut cache, Input::new(rope.chunks()))
        .map(|range| rope.byte_slice(range.range()))
        .collect();
    println!("found {matches:#?} in syntax.rs");
    assert_eq!(matches.len(), 68);
}

#[test]
fn any() {
    let haystack = " ";
    let needle = ".";
    let foo = ropey::Rope::from_str(haystack);
    let regex =
        PikeVM::builder().syntax(Config::new().case_insensitive(true)).build(needle).unwrap();
    let mut cache1 = regex.create_cache();
    let mut cache2 = Cache::new(&regex);
    let iter1: Vec<_> = regex.find_iter(&mut cache1, haystack).collect();
    let iter2: Vec<_> = find_iter(&regex, &mut cache2, Input::new(foo.chunks())).collect();
    assert_eq!(iter1, iter2);
}

#[test]
fn unicode_word_bounderies() {
    let haystack: String = (0..(5 * 4096))
        .map(|i| format!("foöbar  foÖ{0}bar foö{0}bar", " ".repeat(i % 31)))
        .collect();
    let needle = r"\bfoö\b[ ]*\bbar\b";
    let foo = ropey::Rope::from_str(&haystack);
    let regex =
        PikeVM::builder().syntax(Config::new().case_insensitive(true)).build(needle).unwrap();
    let mut cache1 = regex.create_cache();
    let mut cache2 = Cache::new(&regex);
    let iter1: Vec<_> = regex.find_iter(&mut cache1, &haystack).collect();
    let iter2: Vec<_> = find_iter(&regex, &mut cache2, Input::new(foo.chunks())).collect();
    assert_eq!(iter1, iter2);
}
#[test]
fn maybe_empty() {
    let haystack = "x";
    let needle = r"x*";
    let foo = ropey::Rope::from_str(haystack);
    let regex =
        PikeVM::builder().syntax(Config::new().case_insensitive(true)).build(needle).unwrap();
    let mut cache1 = regex.create_cache();
    let mut cache2 = Cache::new(&regex);
    let iter1: Vec<_> = regex.find_iter(&mut cache1, haystack).collect();
    let iter2: Vec<_> = find_iter(&regex, &mut cache2, Input::new(foo.chunks())).collect();
    assert_eq!(iter1, iter2);
}

#[test]
fn maybe_empty2() {
    let haystack = "x";
    let needle = r"\bx*\b";
    let foo = ropey::Rope::from_str(haystack);
    let regex =
        PikeVM::builder().syntax(Config::new().case_insensitive(true)).build(needle).unwrap();
    let mut cache1 = regex.create_cache();
    let mut cache2 = Cache::new(&regex);
    let iter1: Vec<_> = regex.find_iter(&mut cache1, haystack).collect();
    let iter2: Vec<_> = find_iter(&regex, &mut cache2, Input::new(foo.chunks())).collect();
    assert_eq!(iter1, iter2);
}

proptest! {
  #[test]
  fn matches(haystack: String, needle: String) {
    let foo = ropey::Rope::from_str(&haystack);
    let Ok(regex) = PikeVM::builder().syntax(Config::new().case_insensitive(true)).build(&needle) else {
        return Ok(())
    };
    let mut cache1 = regex.create_cache();
    let mut cache2 = Cache::new(&regex);
    let iter1: Vec<_> = regex.find_iter(&mut cache1, &haystack).collect();
    let iter2: Vec<_> = find_iter(&regex, &mut cache2, Input::new(foo.chunks())).collect();
    prop_assert_eq!(iter1, iter2);
  }
  #[test]
  fn matches_word(haystack: String, needle in r"\\b\PC+\\b") {
    let foo = ropey::Rope::from_str(&haystack);
    let Ok(regex) = PikeVM::builder().syntax(Config::new().case_insensitive(true)).build(&needle) else {
        return Ok(())
    };
    let mut cache1 = regex.create_cache();
    let mut cache2 = Cache::new(&regex);
    let iter1: Vec<_> = regex.find_iter(&mut cache1, &haystack).collect();
    let iter2: Vec<_> = find_iter(&regex, &mut cache2, Input::new(foo.chunks())).collect();
    prop_assert_eq!(iter1, iter2);
  }
}
