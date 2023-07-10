use proptest::{prop_assert, proptest};

use crate::engines::hybrid::find_iter;
use crate::input::Input;

#[test]
fn searcher() {
    let text =
        std::fs::read_to_string("/home/pascalkuthe/Projects/helix/master/helix-core/src/syntax.rs")
            .unwrap();
    let regex = super::Regex::builder()
        .syntax(regex_automata::util::syntax::Config::new().case_insensitive(true))
        .build("vec")
        .unwrap();
    let mut cache = regex.create_cache();
    let rope = ropey::Rope::from_str(&text);
    let matches = super::find_iter(&regex, &mut cache, Input::new(rope.slice(..))).count();
    println!("found {matches} in syntax.rs");
    assert_eq!(matches, 68);
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
    let iter1 = regex.find_iter(&mut cache1, &haystack);
    let iter2 = find_iter(&regex, &mut cache2, foo.slice(..));
    prop_assert!(iter1.eq(iter2));
  }
}
