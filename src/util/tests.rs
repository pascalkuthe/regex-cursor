use crate::util::{decode, decode_last};
use crate::Input;
use proptest::{prop_assert_eq, proptest};
use std::iter::successors;

proptest! {
    #[test]
    fn test_decode(haystack: String) {
        let foo = ropey::Rope::from_str(&haystack);
        let mut input = Input::new(foo.slice(..));
        let first_char = decode(&mut input, 0).transpose().unwrap();
        let res: Vec<_> = successors(first_char.map(|c| (0, c)), |(i, c)| {
            decode(&mut input, i + c.len_utf8())
                .transpose()
                .unwrap()
                .map(|c2| (i + c.len_utf8(), c2))
        })
        .collect();
        let ref_chars: Vec<_> = haystack.char_indices().collect();
        prop_assert_eq!(res, ref_chars);

        // let last_char = decode_last(&[], &mut input, 0).transpose().unwrap();
        // let chars_rev = std::iter::successors(first_char.map(|c| (0, c)), |(i, c)| {
        //     decode(&mut input, i + c.len_utf8())
        //         .transpose()
        //         .unwrap()
        //         .map(|c2| (i + c.len_utf8(), c2))
        // });
    }
    #[test]
    fn test_decode_last(haystack: String) {
        let foo = ropey::Rope::from_str(&haystack);
        let mut input = Input::new(foo.slice(..));
        let end = haystack.len();
        input.move_to(end);
        let first_char = decode_last(haystack[..input.haystack_off()].as_bytes(), &mut input, end).transpose().unwrap();
        let res: Vec<_> = successors(first_char.map(|c| (end - c.len_utf8(), c)), |&(i, _)| {
            input.move_to(i);
            decode_last(haystack[..input.haystack_off()].as_bytes(), &mut input, i)
                .transpose()
                .unwrap()
                .map(|c2| (i - c2.len_utf8(), c2))
        })
        .collect();
        let ref_chars: Vec<_> = haystack.char_indices().rev().collect();
        prop_assert_eq!(res, ref_chars);

        // let last_char = decode_last(&[], &mut input, 0).transpose().unwrap();
        // let chars_rev = std::iter::successors(first_char.map(|c| (0, c)), |(i, c)| {
        //     decode(&mut input, i + c.len_utf8())
        //         .transpose()
        //         .unwrap()
        //         .map(|c2| (i + c.len_utf8(), c2))
        // });
    }
}
