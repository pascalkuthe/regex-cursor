use proptest::{prop_assert, prop_assert_eq, proptest};

use crate::engines::hybrid::find_iter;
use crate::input::Input;

#[test]
fn smoke_test() {
    let text = std::fs::read_to_string("test_cases/syntax.rs").unwrap();
    let regex = super::PikeVM::builder()
        .syntax(regex_automata::util::syntax::Config::new().case_insensitive(true))
        .build("vec")
        .unwrap();
    let mut cache = regex.create_cache();
    let rope = ropey::Rope::from_str(&text);
    let matches: Vec<_> = regex
        .find_iter(&mut cache, Input::new(rope.slice(..)))
        .map(|range| rope.byte_slice(range.range()))
        .collect();
    println!("found {matches:#?} in syntax.rs");
    assert_eq!(matches.len(), 68);
}

#[test]
fn unicode_word_bounderies() {
    let haystack: String = (0..(5 * 4096))
        .map(|i| format!("foöbar  foÖ{0}bar foö{0}bar", " ".repeat(i % 31)))
        .collect();
    let needle = r"\bfoö\b[ ]*\bbar\b";
    let foo = ropey::Rope::from_str(&haystack);
    let regex1 = regex_automata::nfa::thompson::pikevm::PikeVM::builder()
        .syntax(regex_automata::util::syntax::Config::new().case_insensitive(true))
        .build(&needle)
        .unwrap();
    let regex2 = super::PikeVM::builder()
        .syntax(regex_automata::util::syntax::Config::new().case_insensitive(true))
        .build(&needle)
        .unwrap();
    let mut cache1 = regex1.create_cache();
    let mut cache2 = regex2.create_cache();
    let iter1: Vec<_> = regex1.find_iter(&mut cache1, &haystack).collect();
    let iter2: Vec<_> = regex2.find_iter(&mut cache2, foo.slice(..)).collect();
    assert_eq!(iter1, iter2);
}
#[test]
fn maybe_empty() {
    let haystack = "x";
    let needle = r"x*";
    let foo = ropey::Rope::from_str(&haystack);
    let regex1 = regex_automata::nfa::thompson::pikevm::PikeVM::builder()
        .syntax(regex_automata::util::syntax::Config::new().case_insensitive(true))
        .build(&needle)
        .unwrap();
    let regex2 = super::PikeVM::builder()
        .syntax(regex_automata::util::syntax::Config::new().case_insensitive(true))
        .build(&needle)
        .unwrap();
    let mut cache1 = regex1.create_cache();
    let mut cache2 = regex2.create_cache();
    let iter1: Vec<_> = regex1.find_iter(&mut cache1, &haystack).collect();
    let iter2: Vec<_> = regex2.find_iter(&mut cache2, foo.slice(..)).collect();
    assert_eq!(iter1, iter2);
}

#[test]
fn maybe_empty2() {
    let haystack = "x";
    let needle = r"\bx*\b";
    let foo = ropey::Rope::from_str(&haystack);
    let regex1 = regex_automata::nfa::thompson::pikevm::PikeVM::builder()
        .syntax(regex_automata::util::syntax::Config::new().case_insensitive(true))
        .build(&needle)
        .unwrap();
    let regex2 = super::PikeVM::builder()
        .syntax(regex_automata::util::syntax::Config::new().case_insensitive(true))
        .build(&needle)
        .unwrap();
    let mut cache1 = regex1.create_cache();
    let mut cache2 = regex2.create_cache();
    let iter1: Vec<_> = regex1.find_iter(&mut cache1, &haystack).collect();
    let iter2: Vec<_> = regex2.find_iter(&mut cache2, foo.slice(..)).collect();
    assert_eq!(iter1, iter2);
}

proptest! {
  #[test]
  fn matches(haystack: String, needle: String) {
    let foo = ropey::Rope::from_str(&haystack);
    let Ok(regex1) = regex_automata::nfa::thompson::pikevm::PikeVM::builder()
        .syntax(regex_automata::util::syntax::Config::new()
            .case_insensitive(true)
        )
        .build(&needle) else {
        return Ok(())
    };
    let Ok(regex2) = super::PikeVM::builder()
        .syntax(regex_automata::util::syntax::Config::new()
            .case_insensitive(true)
        )
        .build(&needle) else {
        return Ok(())
    };
    let mut cache1 = regex1.create_cache();
    let mut cache2 = regex2.create_cache();
    let iter1: Vec<_> = regex1.find_iter(&mut cache1, &haystack).collect();
    let iter2: Vec<_> = regex2.find_iter(&mut cache2, foo.slice(..)).collect();
    prop_assert_eq!(iter1, iter2);
  }
  #[test]
  fn matches_word(haystack: String, needle in r"\\b\PC+\\b") {
    let foo = ropey::Rope::from_str(&haystack);
    let Ok(regex1) = regex_automata::nfa::thompson::pikevm::PikeVM::builder()
        .syntax(regex_automata::util::syntax::Config::new()
            .case_insensitive(true)
        )
        .build(&needle) else {
        return Ok(())
    };
    let Ok(regex2) = super::PikeVM::builder()
        .syntax(regex_automata::util::syntax::Config::new()
            .case_insensitive(true)
        )
        .build(&needle) else {
        return Ok(())
    };
    let mut cache1 = regex1.create_cache();
    let mut cache2 = regex2.create_cache();
    let iter1: Vec<_> = regex1.find_iter(&mut cache1, &haystack).collect();
    let iter2: Vec<_> = regex2.find_iter(&mut cache2, foo.slice(..)).collect();
    prop_assert_eq!(iter1, iter2);
  }
}
