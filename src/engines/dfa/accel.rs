use crate::cursor::Cursor;
use crate::Input;

/// Search for between 1 and 3 needle bytes in the given haystack, starting the
/// search at the given position. If `needles` has a length other than 1-3,
/// then this panics.
#[cfg_attr(feature = "perf-inline", inline(always))]
pub(crate) fn find_fwd_imp(needles: &[u8], haystack: &[u8], at: usize) -> Option<usize> {
    let bs = needles;
    let i = match needles.len() {
        1 => memchr::memchr(bs[0], &haystack[at..])?,
        2 => memchr::memchr2(bs[0], bs[1], &haystack[at..])?,
        3 => memchr::memchr3(bs[0], bs[1], bs[2], &haystack[at..])?,
        0 => panic!("cannot find with empty needles"),
        n => panic!("invalid needles length: {}", n),
    };
    Some(at + i)
}
/// Search for between 1 and 3 needle bytes in the given input, starting the
/// search at the given position. If `needles` has a length other than 1-3,
/// then this panics.
#[cfg_attr(feature = "perf-inline", inline(always))]
pub(crate) fn find_fwd<C: Cursor>(
    needles: &[u8],
    input: &mut Input<C>,
    at: usize,
) -> Option<usize> {
    if let Some(pos) = find_fwd_imp(needles, input.chunk(), at) {
        return Some(pos);
    }
    while input.advance() {
        if let Some(pos) = find_fwd_imp(needles, input.chunk(), 0) {
            return Some(pos);
        }
    }
    None
}

/// Search for between 1 and 3 needle bytes in the given haystack in reverse,
/// starting the search at the given position. If `needles` has a length other
/// than 1-3, then this panics.
#[cfg_attr(feature = "perf-inline", inline(always))]
pub(crate) fn find_rev_imp(needles: &[u8], haystack: &[u8], at: usize) -> Option<usize> {
    let bs = needles;
    match needles.len() {
        1 => memchr::memrchr(bs[0], &haystack[..at]),
        2 => memchr::memrchr2(bs[0], bs[1], &haystack[..at]),
        3 => memchr::memrchr3(bs[0], bs[1], bs[2], &haystack[..at]),
        0 => panic!("cannot find with empty needles"),
        n => panic!("invalid needles length: {}", n),
    }
}
/// Search for between 1 and 3 needle bytes in the given input, starting the
/// search at the given position. If `needles` has a length other than 1-3,
/// then this panics.
#[cfg_attr(feature = "perf-inline", inline(always))]
pub(crate) fn find_rev<C: Cursor>(
    needles: &[u8],
    input: &mut Input<C>,
    at: usize,
) -> Option<usize> {
    if let Some(pos) = find_rev_imp(needles, input.chunk(), at) {
        return Some(pos);
    }
    while input.backtrack() {
        if let Some(pos) = find_rev_imp(needles, input.chunk(), input.chunk().len()) {
            return Some(pos);
        }
    }
    None
}
