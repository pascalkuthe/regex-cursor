pub use regex_automata::dfa::regex::Regex;
use regex_automata::dfa::Automaton;
use regex_automata::{Anchored, Match, MatchError};

use crate::cursor::Cursor;
use crate::util::iter;
use crate::Input;

pub use crate::engines::dfa::search::{try_search_fwd, try_search_rev};

mod accel;
mod search;
#[cfg(test)]
mod test;

/// Returns true if either the given input specifies an anchored search
/// or if the underlying NFA is always anchored.
fn is_anchored(regex: &Regex, input: &Input<impl Cursor>) -> bool {
    match input.get_anchored() {
        Anchored::No => regex.forward().is_always_start_anchored(),
        Anchored::Yes | Anchored::Pattern(_) => true,
    }
}

/// Returns an iterator over all non-overlapping leftmost matches in the
/// given bytes. If no match exists, then the iterator yields no elements.
///
/// # Panics
///
/// This routine panics if the search could not complete. This can occur
/// in a number of circumstances:
///
/// * The configuration of the lazy DFA may permit it to "quit" the search.
/// For example, setting quit bytes or enabling heuristic support for
/// Unicode word boundaries. The default configuration does not enable any
/// option that could result in the lazy DFA quitting.
/// * The configuration of the lazy DFA may also permit it to "give up"
/// on a search if it makes ineffective use of its transition table
/// cache. The default configuration does not enable this by default,
/// although it is typically a good idea to.
/// * When the provided `Input` configuration is not supported. For
/// example, by providing an unsupported anchor mode.
///
/// When a search panics, callers cannot know whether a match exists or
/// not.
///
/// The above conditions also apply to the iterator returned as well. For
/// example, if the lazy DFA gives up or quits during a search using this
/// method, then a panic will occur during iteration.
///
/// Use [`Regex::try_search`] with [`util::iter::Searcher`](iter::Searcher)
/// if you want to handle these error conditions.
///
/// # Example
///
/// ```
/// use regex_automata::{hybrid::regex::Regex, Match};
///
/// let re = Regex::new("foo[0-9]+")?;
/// let mut cache = re.create_cache();
///
/// let text = "foo1 foo12 foo123";
/// let matches: Vec<Match> = re.find_iter(&mut cache, text).collect();
/// assert_eq!(matches, vec![
///     Match::must(0, 0..4),
///     Match::must(0, 5..10),
///     Match::must(0, 11..17),
/// ]);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[inline]
pub fn find_iter<C: Cursor>(regex: &Regex, input: Input<C>) -> FindMatches<'_, C> {
    let it = iter::Searcher::new(input);
    FindMatches { re: regex, it }
}

/// Returns the start and end offset of the leftmost match. If no match
/// exists, then `None` is returned.
///
/// # Panics
///
/// This routine panics if the search could not complete. This can occur
/// in a number of circumstances:
///
/// * The configuration of the lazy DFA may permit it to "quit" the search.
/// For example, setting quit bytes or enabling heuristic support for
/// Unicode word boundaries. The default configuration does not enable any
/// option that could result in the lazy DFA quitting.
/// * The configuration of the lazy DFA may also permit it to "give up"
/// on a search if it makes ineffective use of its transition table
/// cache. The default configuration does not enable this by default,
/// although it is typically a good idea to.
/// * When the provided `Input` configuration is not supported. For
/// example, by providing an unsupported anchor mode.
///
/// When a search panics, callers cannot know whether a match exists or
/// not.
///
/// Use [`Regex::try_search`] if you want to handle these error conditions.
///
/// # Example
///
/// ```
/// use regex_automata::{Match, hybrid::regex::Regex};
///
/// let re = Regex::new("foo[0-9]+")?;
/// let mut cache = re.create_cache();
/// assert_eq!(
///     Some(Match::must(0, 3..11)),
///     re.find(&mut cache, "zzzfoo12345zzz"),
/// );
///
/// // Even though a match is found after reading the first byte (`a`),
/// // the default leftmost-first match semantics demand that we find the
/// // earliest match that prefers earlier parts of the pattern over latter
/// // parts.
/// let re = Regex::new("abc|a")?;
/// let mut cache = re.create_cache();
/// assert_eq!(Some(Match::must(0, 0..3)), re.find(&mut cache, "abc"));
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub fn find<C: Cursor>(regex: &Regex, input: &mut Input<C>) -> Option<Match> {
    try_search(regex, input).unwrap()
}

/// Returns the start and end offset of the leftmost match. If no match
/// exists, then `None` is returned.
///
/// This is like [`Regex::find`] but with two differences:
///
/// 1. It is not generic over `Into<Input>` and instead accepts a
/// `&Input`. This permits reusing the same `Input` for multiple searches
/// without needing to create a new one. This _may_ help with latency.
/// 2. It returns an error if the search could not complete where as
/// [`Regex::find`] will panic.
///
/// # Errors
///
/// This routine errors if the search could not complete. This can occur
/// in a number of circumstances:
///
/// * The configuration of the lazy DFA may permit it to "quit" the search.
/// For example, setting quit bytes or enabling heuristic support for
/// Unicode word boundaries. The default configuration does not enable any
/// option that could result in the lazy DFA quitting.
/// * The configuration of the lazy DFA may also permit it to "give up"
/// on a search if it makes ineffective use of its transition table
/// cache. The default configuration does not enable this by default,
/// although it is typically a good idea to.
/// * When the provided `Input` configuration is not supported. For
/// example, by providing an unsupported anchor mode.
///
/// When a search returns an error, callers cannot know whether a match
/// exists or not.
pub fn try_search<C: Cursor>(
    regex: &Regex,
    input: &mut Input<C>,
) -> Result<Option<Match>, MatchError> {
    let fwd = regex.forward();
    let end = match try_search_fwd(fwd, input)? {
        None => return Ok(None),
        Some(end) => end,
    };
    // This special cases an empty match at the beginning of the search. If
    // our end matches our start, then since a reverse DFA can't match past
    // the start, it must follow that our starting position is also our end
    // position. So short circuit and skip the reverse search.
    if input.start() == end.offset() {
        return Ok(Some(Match::new(end.pattern(), end.offset()..end.offset())));
    }
    // We can also skip the reverse search if we know our search was
    // anchored. This occurs either when the input config is anchored or
    // when we know the regex itself is anchored. In this case, we know the
    // start of the match, if one is found, must be the start of the
    // search.
    if is_anchored(regex, input) {
        return Ok(Some(Match::new(end.pattern(), input.start()..end.offset())));
    }
    // N.B. I have tentatively convinced myself that it isn't necessary
    // to specify the specific pattern for the reverse search since the
    // reverse search will always find the same pattern to match as the
    // forward search. But I lack a rigorous proof. Why not just provide
    // the pattern anyway? Well, if it is needed, then leaving it out
    // gives us a chance to find a witness. (Also, if we don't need to
    // specify the pattern, then we don't need to build the reverse DFA
    // with 'starts_for_each_pattern' enabled. It doesn't matter too much
    // for the lazy DFA, but does make the overall DFA bigger.)
    //
    // We also need to be careful to disable 'earliest' for the reverse
    // search, since it could be enabled for the forward search. In the
    // reverse case, to satisfy "leftmost" criteria, we need to match as
    // much as we can. We also need to be careful to make the search
    // anchored. We don't want the reverse search to report any matches
    // other than the one beginning at the end of our forward search.

    let match_range = input.start()..end.offset();
    let start = input.with(|mut revsearch| {
        revsearch = revsearch.span(match_range).anchored(Anchored::Yes).earliest(false);
        try_search_rev(regex.reverse(), revsearch)
    });
    let start = start?.expect("reverse search must match if forward search does");
    debug_assert_eq!(
        start.pattern(),
        end.pattern(),
        "forward and reverse search must match same pattern",
    );
    debug_assert!(start.offset() <= end.offset());
    debug_assert!(end.offset() <= input.end());
    debug_assert!(input.start() <= start.offset());
    Ok(Some(Match::new(end.pattern(), start.offset()..end.offset())))
}

/// An iterator over all non-overlapping matches for an infallible search.
///
/// The iterator yields a [`Match`] value until no more matches could be found.
/// If the underlying regex engine returns an error, then a panic occurs.
///
/// This iterator can be created with the [`Regex::find_iter`] method.
#[derive(Debug)]
pub struct FindMatches<'r, C: Cursor> {
    re: &'r Regex,
    it: iter::Searcher<C>,
}

impl<'r, C: Cursor> Iterator for FindMatches<'r, C> {
    type Item = Match;

    #[inline]
    fn next(&mut self) -> Option<Match> {
        let FindMatches { re, ref mut it } = *self;
        it.advance(|input| try_search(re, input))
    }
}
