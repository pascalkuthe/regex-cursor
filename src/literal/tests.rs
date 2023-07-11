// use proptest::proptest;

// proptest! {
//   #[test]
//   fn matches(haystack: String, needle in "\\PC{0,29}") {
//         let foo = ropey::Rope::from_str(&haystack);
//     let filter1 = super::Prefilter::new(regex_automata::MatchKind::All, &[needle]).unwrap();
//     let filter2 = regex_automata::util::prefilter::Prefilter::new(regex_automata::MatchKind::All, &[needle]).unwrap();
//     let mut cache1 = regex.create_cache();
//     let mut cache2 = regex.create_cache();
//     let iter1 = regex.find_iter(&mut cache1, &haystack);
//     let iter2 = find_iter(&regex, &mut cache2, foo.slice(..));
//     prop_assert!(iter1.eq(iter2));
//   }
// }
