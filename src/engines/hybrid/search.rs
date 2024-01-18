use regex_automata::hybrid::dfa::{Cache, DFA};
use regex_automata::hybrid::{LazyStateID, StartError};
use regex_automata::util::prefilter::Prefilter;
use regex_automata::util::start;
use regex_automata::{HalfMatch, MatchError};

use crate::cursor::Cursor;
use crate::input::Input;
use crate::literal;
use crate::util::empty::{skip_splits_fwd, skip_splits_rev};

/// Executes a forward search and returns the end position of the leftmost
/// match that is found. If no match exists, then `None` is returned.
///
/// In particular, this method continues searching even after it enters
/// a match state. The search only terminates once it has reached the
/// end of the input or when it has entered a dead or quit state. Upon
/// termination, the position of the last byte seen while still in a match
/// state is returned.
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
///
/// # Example
///
/// This example shows how to run a basic search.
///
/// ```
/// use regex_automata::{hybrid::dfa::DFA, HalfMatch, Input};
///
/// let dfa = DFA::new("foo[0-9]+")?;
/// let mut cache = dfa.create_cache();
/// let expected = HalfMatch::must(0, 8);
/// assert_eq!(Some(expected), dfa.try_search_fwd(
///     &mut cache, &mut Input::new("foo12345"))?,
/// );
///
/// // Even though a match is found after reading the first byte (`a`),
/// // the leftmost first match semantics demand that we find the earliest
/// // match that prefers earlier parts of the pattern over later parts.
/// let dfa = DFA::new("abc|a")?;
/// let mut cache = dfa.create_cache();
/// let expected = HalfMatch::must(0, 3);
/// assert_eq!(Some(expected), dfa.try_search_fwd(
///     &mut cache, &mut Input::new("abc"))?,
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Example: specific pattern search
///
/// This example shows how to build a lazy multi-DFA that permits searching
/// for specific patterns.
///
/// ```
/// use regex_automata::{
///     hybrid::dfa::DFA,
///     Anchored, HalfMatch, PatternID, Input,
/// };
///
/// let dfa = DFA::builder()
///     .configure(DFA::config().starts_for_each_pattern(true))
///     .build_many(&["[a-z0-9]{6}", "[a-z][a-z0-9]{5}"])?;
/// let mut cache = dfa.create_cache();
/// let haystack = "foo123";
///
/// // Since we are using the default leftmost-first match and both
/// // patterns match at the same starting position, only the first pattern
/// // will be returned in this case when doing a search for any of the
/// // patterns.
/// let expected = Some(HalfMatch::must(0, 6));
/// let got = dfa.try_search_fwd(&mut cache, &mut Input::new(haystack))?;
/// assert_eq!(expected, got);
///
/// // But if we want to check whether some other pattern matches, then we
/// // can provide its pattern ID.
/// let expected = Some(HalfMatch::must(1, 6));
/// let input = Input::new(haystack)
///     .anchored(Anchored::Pattern(PatternID::must(1)));
/// let got = dfa.try_search_fwd(&mut cache, &input)?;
/// assert_eq!(expected, got);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Example: specifying the bounds of a search
///
/// This example shows how providing the bounds of a search can produce
/// different results than simply sub-slicing the haystack.
///
/// ```
/// use regex_automata::{hybrid::dfa::DFA, HalfMatch, Input};
///
/// // N.B. We disable Unicode here so that we use a simple ASCII word
/// // boundary. Alternatively, we could enable heuristic support for
/// // Unicode word boundaries since our haystack is pure ASCII.
/// let dfa = DFA::new(r"(?-u)\b[0-9]{3}\b")?;
/// let mut cache = dfa.create_cache();
/// let haystack = "foo123bar";
///
/// // Since we sub-slice the haystack, the search doesn't know about the
/// // larger context and assumes that `123` is surrounded by word
/// // boundaries. And of course, the match position is reported relative
/// // to the sub-slice as well, which means we get `3` instead of `6`.
/// let expected = Some(HalfMatch::must(0, 3));
/// let got = dfa.try_search_fwd(
///     &mut cache,
///     &mut Input::new(&haystack[3..6]),
/// )?;
/// assert_eq!(expected, got);
///
/// // But if we provide the bounds of the search within the context of the
/// // entire haystack, then the search can take the surrounding context
/// // into account. (And if we did find a match, it would be reported
/// // as a valid offset into `haystack` instead of its sub-slice.)
/// let expected = None;
/// let got = dfa.try_search_fwd(
///     &mut cache,
///     &mut Input::new(haystack).range(3..6),
/// )?;
/// assert_eq!(expected, got);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[inline]
pub fn try_search_fwd<C: Cursor>(
    dfa: &DFA,
    cache: &mut Cache,
    input: &mut Input<C>,
) -> Result<Option<HalfMatch>, MatchError> {
    let utf8empty = dfa.get_nfa().has_empty() && dfa.get_nfa().is_utf8();
    let hm = match find_fwd(dfa, cache, input)? {
        None => return Ok(None),
        Some(hm) if !utf8empty => return Ok(Some(hm)),
        Some(hm) => hm,
    };
    // We get to this point when we know our DFA can match the empty string
    // AND when UTF-8 mode is enabled. In this case, we skip any matches
    // whose offset splits a codepoint. Such a match is necessarily a
    // zero-width match, because UTF-8 mode requires the underlying NFA
    // to be built such that all non-empty matches span valid UTF-8.
    // Therefore, any match that ends in the middle of a codepoint cannot
    // be part of a span of valid UTF-8 and thus must be an empty match.
    // In such cases, we skip it, so as not to report matches that split a
    // codepoint.
    //
    // Note that this is not a checked assumption. Callers *can* provide an
    // NFA with UTF-8 mode enabled but produces non-empty matches that span
    // invalid UTF-8. But doing so is documented to result in unspecified
    // behavior.
    skip_splits_fwd(input, hm, hm.offset(), |input| {
        let got = find_fwd(dfa, cache, input)?;
        Ok(got.map(|hm| (hm, hm.offset())))
    })
}

/// Executes a reverse search and returns the start of the position of the
/// leftmost match that is found. If no match exists, then `None` is
/// returned.
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
///
/// # Example
///
/// This routine is principally useful when used in
/// conjunction with the
/// [`nfa::thompson::Config::reverse`](crate::nfa::thompson::Config::reverse)
/// configuration. In general, it's unlikely to be correct to use both
/// `try_search_fwd` and `try_search_rev` with the same DFA since any
/// particular DFA will only support searching in one direction with
/// respect to the pattern.
///
/// ```
/// use regex_automata::{
///     nfa::thompson,
///     hybrid::dfa::DFA,
///     HalfMatch, Input,
/// };
///
/// let dfa = DFA::builder()
///     .thompson(thompson::Config::new().reverse(true))
///     .build("foo[0-9]+")?;
/// let mut cache = dfa.create_cache();
/// let expected = HalfMatch::must(0, 0);
/// assert_eq!(
///     Some(expected),
///     dfa.try_search_rev(&mut cache, &mut Input::new("foo12345"))?,
/// );
///
/// // Even though a match is found after reading the last byte (`c`),
/// // the leftmost first match semantics demand that we find the earliest
/// // match that prefers earlier parts of the pattern over latter parts.
/// let dfa = DFA::builder()
///     .thompson(thompson::Config::new().reverse(true))
///     .build("abc|c")?;
/// let mut cache = dfa.create_cache();
/// let expected = HalfMatch::must(0, 0);
/// assert_eq!(Some(expected), dfa.try_search_rev(
///     &mut cache, &mut Input::new("abc"))?,
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Example: UTF-8 mode
///
/// This examples demonstrates that UTF-8 mode applies to reverse
/// DFAs. When UTF-8 mode is enabled in the underlying NFA, then all
/// matches reported must correspond to valid UTF-8 spans. This includes
/// prohibiting zero-width matches that split a codepoint.
///
/// UTF-8 mode is enabled by default. Notice below how the only zero-width
/// matches reported are those at UTF-8 boundaries:
///
/// ```
/// use regex_automata::{
///     hybrid::dfa::DFA,
///     nfa::thompson,
///     HalfMatch, Input, MatchKind,
/// };
///
/// let dfa = DFA::builder()
///     .thompson(thompson::Config::new().reverse(true))
///     .build(r"")?;
/// let mut cache = dfa.create_cache();
///
/// // Run the reverse DFA to collect all matches.
/// let mut input = Input::new("☃");
/// let mut matches = vec![];
/// loop {
///     match dfa.try_search_rev(&mut cache, &input)? {
///         None => break,
///         Some(hm) => {
///             matches.push(hm);
///             if hm.offset() == 0 || input.end() == 0 {
///                 break;
///             } else if hm.offset() < input.end() {
///                 input.set_end(hm.offset());
///             } else {
///                 // This is only necessary to handle zero-width
///                 // matches, which of course occur in this example.
///                 // Without this, the search would never advance
///                 // backwards beyond the initial match.
///                 input.set_end(input.end() - 1);
///             }
///         }
///     }
/// }
///
/// // No matches split a codepoint.
/// let expected = vec![
///     HalfMatch::must(0, 3),
///     HalfMatch::must(0, 0),
/// ];
/// assert_eq!(expected, matches);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// Now let's look at the same example, but with UTF-8 mode on the
/// underlying NFA disabled:
///
/// ```
/// use regex_automata::{
///     hybrid::dfa::DFA,
///     nfa::thompson,
///     HalfMatch, Input, MatchKind,
/// };
///
/// let dfa = DFA::builder()
///     .thompson(thompson::Config::new().reverse(true).utf8(false))
///     .build(r"")?;
/// let mut cache = dfa.create_cache();
///
/// // Run the reverse DFA to collect all matches.
/// let mut input = Input::new("☃");
/// let mut matches = vec![];
/// loop {
///     match dfa.try_search_rev(&mut cache, &input)? {
///         None => break,
///         Some(hm) => {
///             matches.push(hm);
///             if hm.offset() == 0 || input.end() == 0 {
///                 break;
///             } else if hm.offset() < input.end() {
///                 input.set_end(hm.offset());
///             } else {
///                 // This is only necessary to handle zero-width
///                 // matches, which of course occur in this example.
///                 // Without this, the search would never advance
///                 // backwards beyond the initial match.
///                 input.set_end(input.end() - 1);
///             }
///         }
///     }
/// }
///
/// // No matches split a codepoint.
/// let expected = vec![
///     HalfMatch::must(0, 3),
///     HalfMatch::must(0, 2),
///     HalfMatch::must(0, 1),
///     HalfMatch::must(0, 0),
/// ];
/// assert_eq!(expected, matches);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[inline]
pub fn try_search_rev<C: Cursor>(
    dfa: &DFA,
    cache: &mut Cache,
    input: &mut Input<C>,
) -> Result<Option<HalfMatch>, MatchError> {
    let utf8empty = dfa.get_nfa().has_empty() && dfa.get_nfa().is_utf8();
    let hm = match find_rev(dfa, cache, input)? {
        None => return Ok(None),
        Some(hm) if !utf8empty => return Ok(Some(hm)),
        Some(hm) => hm,
    };
    skip_splits_rev(input, hm, hm.offset(), |input| {
        let got = find_rev(dfa, cache, input)?;
        Ok(got.map(|hm| (hm, hm.offset())))
    })
}

#[inline(never)]
pub(crate) fn find_fwd<C: Cursor>(
    dfa: &DFA,
    cache: &mut Cache,
    input: &mut Input<C>,
) -> Result<Option<HalfMatch>, MatchError> {
    input.move_to(input.start());
    if input.is_done() {
        return Ok(None);
    }
    let pre =
        if input.get_anchored().is_anchored() { None } else { dfa.get_config().get_prefilter() };
    // So what we do here is specialize four different versions of 'find_fwd':
    // one for each of the combinations for 'has prefilter' and 'is earliest
    // search'. The reason for doing this is that both of these things require
    // branches and special handling in some code that can be very hot,
    // and shaving off as much as we can when we don't need it tends to be
    // beneficial in ad hoc benchmarks. To see these differences, you often
    // need a query with a high match count. In other words, specializing these
    // four routines *tends* to help latency more than throughput.
    if pre.is_some() {
        if input.get_earliest() {
            find_fwd_imp(dfa, cache, input, pre, true)
        } else {
            find_fwd_imp(dfa, cache, input, pre, false)
        }
    } else if input.get_earliest() {
        find_fwd_imp(dfa, cache, input, None, true)
    } else {
        find_fwd_imp(dfa, cache, input, None, false)
    }
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn find_fwd_imp<C: Cursor>(
    dfa: &DFA,
    cache: &mut Cache,
    input: &mut Input<C>,
    pre: Option<&'_ Prefilter>,
    earliest: bool,
) -> Result<Option<HalfMatch>, MatchError> {
    // See 'prefilter_restart' docs for explanation.
    let universal_start = dfa.get_nfa().look_set_prefix_any().is_empty();
    let mut mat = None;
    let mut sid = init_fwd(dfa, cache, input)?;
    if let Some(pre) = pre {
        // If a prefilter doesn't report false positives, then we don't need to
        // touch the DFA at all. However, since all matches include the pattern
        // ID, and the prefilter infrastructure doesn't report pattern IDs, we
        // limit this optimization to cases where there is exactly one pattern.
        // In that case, any match must be the 0th pattern.
        match literal::find(pre, input) {
            None => return Ok(mat),
            Some(ref span) => {
                input.move_to(span.start);
                if !universal_start {
                    sid = prefilter_restart(dfa, cache, input)?;
                }
            }
        }
    }
    // This could just be a closure, but then I think it would be unsound
    // because it would need to be safe to invoke. This way, the lack of safety
    // is clearer in the code below.
    macro_rules! next_unchecked {
        ($sid:expr) => {{
            debug_assert!(input.chunk_pos() < input.chunk().len());
            let byte = *input.chunk().get_unchecked(input.chunk_pos());
            dfa.next_state_untagged_unchecked(cache, $sid, byte)
        }};
    }

    macro_rules! ensure_chunk {
        () => {{
            if input.chunk_pos() >= input.chunk().len() && !input.advance() {
                break;
            }
        }};
    }

    cache.search_start(input.at());
    while input.at() < input.end() {
        if sid.is_tagged() {
            ensure_chunk!();
            cache.search_update(input.at());
            sid = dfa
                .next_state(cache, sid, input.chunk()[input.chunk_pos])
                .map_err(|_| gave_up(input.at()))?;
        } else {
            // SAFETY: There are two safety invariants we need to uphold
            // here in the loops below: that 'sid' and 'prev_sid' are valid
            // state IDs for this DFA, and that 'at' is a valid index into
            // 'haystack'. For the former, we rely on the invariant that
            // next_state* and start_state_forward always returns a valid state
            // ID (given a valid state ID in the former case), and that we are
            // only at this place in the code if 'sid' is untagged. Moreover,
            // every call to next_state_untagged_unchecked below is guarded by
            // a check that sid is untagged. For the latter safety invariant,
            // we always guard unchecked access with a check that 'at' is less
            // than 'end', where 'end <= haystack.len()'. In the unrolled loop
            // below, we ensure that 'at' is always in bounds.
            //
            // PERF: For justification of omitting bounds checks, it gives us a
            // ~10% bump in search time. This was used for a benchmark:
            //
            //     regex-cli find hybrid dfa @bigfile '(?m)^.+$' -UBb
            //
            // PERF: For justification for the loop unrolling, we use a few
            // different tests:
            //
            //     regex-cli find hybrid dfa @$bigfile '\w{50}' -UBb
            //     regex-cli find hybrid dfa @$bigfile '(?m)^.+$' -UBb
            //     regex-cli find hybrid dfa @$bigfile 'ZQZQZQZQ' -UBb
            //
            // And there are three different configurations:
            //
            //     nounroll: this entire 'else' block vanishes and we just
            //               always use 'dfa.next_state(..)'.
            //      unroll1: just the outer loop below
            //      unroll2: just the inner loop below
            //      unroll3: both the outer and inner loops below
            //
            // This results in a matrix of timings for each of the above
            // regexes with each of the above unrolling configurations:
            //
            //              '\w{50}'   '(?m)^.+$'   'ZQZQZQZQ'
            //   nounroll   1.51s      2.34s        1.51s
            //    unroll1   1.53s      2.32s        1.56s
            //    unroll2   2.22s      1.50s        0.61s
            //    unroll3   1.67s      1.45s        0.61s
            //
            // Ideally we'd be able to find a configuration that yields the
            // best time for all regexes, but alas we settle for unroll3 that
            // gives us *almost* the best for '\w{50}' and the best for the
            // other two regexes.
            //
            // So what exactly is going on here? The first unrolling (grouping
            // together runs of untagged transitions) specifically targets
            // our choice of representation. The second unrolling (grouping
            // together runs of self-transitions) specifically targets a common
            // DFA topology. Let's dig in a little bit by looking at our
            // regexes:
            //
            // '\w{50}': This regex spends a lot of time outside of the DFA's
            // start state matching some part of the '\w' repetition. This
            // means that it's a bit of a worst case for loop unrolling that
            // targets self-transitions since the self-transitions in '\w{50}'
            // are not particularly active for this haystack. However, the
            // first unrolling (grouping together untagged transitions)
            // does apply quite well here since very few transitions hit
            // match/dead/quit/unknown states. It is however worth mentioning
            // that if start states are configured to be tagged (which you
            // typically want to do if you have a prefilter), then this regex
            // actually slows way down because it is constantly ping-ponging
            // out of the unrolled loop and into the handling of a tagged start
            // state below. But when start states aren't tagged, the unrolled
            // loop stays hot. (This is why it's imperative that start state
            // tagging be disabled when there isn't a prefilter!)
            //
            // '(?m)^.+$': There are two important aspects of this regex: 1)
            // on this haystack, its match count is very high, much higher
            // than the other two regex and 2) it spends the vast majority
            // of its time matching '.+'. Since Unicode mode is disabled,
            // this corresponds to repeatedly following self transitions for
            // the vast majority of the input. This does benefit from the
            // untagged unrolling since most of the transitions will be to
            // untagged states, but the untagged unrolling does more work than
            // what is actually required. Namely, it has to keep track of the
            // previous and next state IDs, which I guess requires a bit more
            // shuffling. This is supported by the fact that nounroll+unroll1
            // are both slower than unroll2+unroll3, where the latter has a
            // loop unrolling that specifically targets self-transitions.
            //
            // 'ZQZQZQZQ': This one is very similar to '(?m)^.+$' because it
            // spends the vast majority of its time in self-transitions for
            // the (implicit) unanchored prefix. The main difference with
            // '(?m)^.+$' is that it has a much lower match count. So there
            // isn't much time spent in the overhead of reporting matches. This
            // is the primary explainer in the perf difference here. We include
            // this regex and the former to make sure we have comparison points
            // with high and low match counts.
            //
            // NOTE: I used 'OpenSubtitles2018.raw.sample.en' for 'bigfile'.
            //
            // NOTE: In a follow-up, it turns out that the "inner" loop
            // mentioned above was a pretty big pessimization in some other
            // cases. Namely, it resulted in too much ping-ponging into and out
            // of the loop, which resulted in nearly ~2x regressions in search
            // time when compared to the originaly lazy DFA in the regex crate.
            // So I've removed the second loop unrolling that targets the
            // self-transition case.
            let mut prev_sid = sid;
            while input.at() < input.end() {
                ensure_chunk!();
                prev_sid = unsafe { next_unchecked!(sid) };
                if prev_sid.is_tagged() || input.at() + 3 >= input.end() {
                    core::mem::swap(&mut prev_sid, &mut sid);
                    break;
                }
                input.chunk_pos += 1;
                if input.chunk_pos + 3 >= input.chunk().len() {
                    core::mem::swap(&mut prev_sid, &mut sid);
                    continue;
                }

                sid = unsafe { next_unchecked!(prev_sid) };
                if sid.is_tagged() {
                    break;
                }
                input.chunk_pos += 1;

                prev_sid = unsafe { next_unchecked!(sid) };
                if prev_sid.is_tagged() {
                    core::mem::swap(&mut prev_sid, &mut sid);
                    break;
                }
                input.chunk_pos += 1;

                sid = unsafe { next_unchecked!(prev_sid) };
                if sid.is_tagged() {
                    break;
                }
                input.chunk_pos += 1;
            }
            // If we quit out of the code above with an unknown state ID at
            // any point, then we need to re-compute that transition using
            // 'next_state', which will do NFA powerset construction for us.
            if sid.is_unknown() {
                cache.search_update(input.at());
                sid = dfa
                    .next_state(cache, prev_sid, input.chunk()[input.chunk_pos])
                    .map_err(|_| gave_up(input.at()))?;
            }
        }
        if sid.is_tagged() {
            if sid.is_start() {
                if let Some(pre) = pre {
                    let old_pos = input.at();
                    match literal::find(pre, input) {
                        None => return Ok(mat),
                        Some(ref span) => {
                            // We want to skip any update to 'at' below
                            // at the end of this iteration and just
                            // jump immediately back to the next state
                            // transition at the leading position of the
                            // candidate match.
                            //
                            // ... but only if we actually made progress
                            // with our prefilter, otherwise if the start
                            // state has a self-loop, we can get stuck.
                            if span.start > old_pos {
                                input.move_to(span.start);
                                if !universal_start {
                                    sid = prefilter_restart(dfa, cache, input)?;
                                }
                                continue;
                            }
                        }
                    }
                }
            } else if sid.is_match() {
                let pattern = dfa.match_pattern(cache, sid, 0);
                // Since slice ranges are inclusive at the beginning and
                // exclusive at the end, and since forward searches report
                // the end, we can return 'at' as-is. This only works because
                // matches are delayed by 1 byte. So by the time we observe a
                // match, 'at' has already been set to 1 byte past the actual
                // match location, which is precisely the exclusive ending
                // bound of the match.
                mat = Some(HalfMatch::new(pattern, input.at()));
                if earliest {
                    cache.search_finish(input.at());
                    return Ok(mat);
                }
            } else if sid.is_dead() {
                cache.search_finish(input.at());
                return Ok(mat);
            } else if sid.is_quit() {
                cache.search_finish(input.at());
            } else {
                debug_assert!(sid.is_unknown());
                unreachable!("sid being unknown is a bug");
            }
        }
        input.chunk_pos += 1;
    }
    eoi_fwd(dfa, cache, input, &mut sid, &mut mat)?;
    cache.search_finish(input.end());
    Ok(mat)
}

#[inline(never)]
pub(crate) fn find_rev<C: Cursor>(
    dfa: &DFA,
    cache: &mut Cache,
    input: &mut Input<C>,
) -> Result<Option<HalfMatch>, MatchError> {
    input.move_to(input.end());
    if input.is_done() {
        return Ok(None);
    }
    if input.get_earliest() {
        find_rev_imp(dfa, cache, input, true)
    } else {
        find_rev_imp(dfa, cache, input, false)
    }
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn find_rev_imp<C: Cursor>(
    dfa: &DFA,
    cache: &mut Cache,
    input: &mut Input<C>,
    earliest: bool,
) -> Result<Option<HalfMatch>, MatchError> {
    let mut mat = None;
    let mut sid = init_rev(dfa, cache, input)?;
    // In reverse search, the loop below can't handle the case of searching an
    // empty slice. Ideally we could write something congruent to the forward
    // search, i.e., 'while at >= start', but 'start' might be 0. Since we use
    // an unsigned offset, 'at >= 0' is trivially always true. We could avoid
    // this extra case handling by using a signed offset, but Rust makes it
    // annoying to do. So... We just handle the empty case separately.
    if input.start() == input.end() || input.chunk_pos == 0 && !input.backtrack() {
        eoi_rev(dfa, cache, input, &mut sid, &mut mat)?;
        return Ok(mat);
    }
    input.chunk_pos -= 1;

    // This could just be a closure, but then I think it would be unsound
    // because it would need to be safe to invoke. This way, the lack of safety
    // is clearer in the code below.
    macro_rules! next_unchecked {
        ($sid:expr) => {{
            let byte = *input.chunk().get_unchecked(input.chunk_pos);
            dfa.next_state_untagged_unchecked(cache, $sid, byte)
        }};
    }
    #[rustfmt::skip]
    macro_rules! ensure_chunk {
        () => {
            if input.chunk_pos == 0 && !input.backtrack() {
                break;
            }
        };
    }
    cache.search_start(input.at());
    loop {
        if sid.is_tagged() {
            cache.search_update(input.at());
            sid = dfa
                .next_state(cache, sid, input.chunk()[input.chunk_pos])
                .map_err(|_| gave_up(input.at()))?;
        } else {
            // SAFETY: See comments in 'find_fwd' for a safety argument.
            //
            // PERF: The comments in 'find_fwd' also provide a justification
            // from a performance perspective as to 1) why we elide bounds
            // checks and 2) why we do a specialized version of unrolling
            // below. The reverse search does have a slightly different
            // consideration in that most reverse searches tend to be
            // anchored and on shorter haystacks. However, this still makes a
            // difference. Take this command for example:
            //
            //     regex-cli find hybrid regex @$bigfile '(?m)^.+$' -UBb
            //
            // (Notice that we use 'find hybrid regex', not 'find hybrid dfa'
            // like in the justification for the forward direction. The 'regex'
            // sub-command will find start-of-match and thus run the reverse
            // direction.)
            //
            // Without unrolling below, the above command takes around 3.76s.
            // But with the unrolling below, we get down to 2.55s. If we keep
            // the unrolling but add in bounds checks, then we get 2.86s.
            //
            // NOTE: I used 'OpenSubtitles2018.raw.sample.en' for 'bigfile'.
            let mut prev_sid = sid;
            while input.at() >= input.start() {
                prev_sid = unsafe { next_unchecked!(sid) };
                if prev_sid.is_tagged() || input.at() <= input.start().saturating_add(3) {
                    core::mem::swap(&mut prev_sid, &mut sid);
                    break;
                }
                ensure_chunk!();
                input.chunk_pos -= 1;
                if input.chunk_pos <= 2 {
                    core::mem::swap(&mut prev_sid, &mut sid);
                    continue;
                }

                sid = unsafe { next_unchecked!(prev_sid) };
                if sid.is_tagged() {
                    break;
                }
                input.chunk_pos -= 1;

                prev_sid = unsafe { next_unchecked!(sid) };
                if prev_sid.is_tagged() {
                    core::mem::swap(&mut prev_sid, &mut sid);
                    break;
                }
                input.chunk_pos -= 1;

                sid = unsafe { next_unchecked!(prev_sid) };
                if sid.is_tagged() {
                    break;
                }
                input.chunk_pos -= 1;
            }
            // If we quit out of the code above with an unknown state ID at
            // any point, then we need to re-compute that transition using
            // 'next_state', which will do NFA powerset construction for us.
            if sid.is_unknown() {
                cache.search_update(input.at());
                sid = dfa
                    .next_state(cache, prev_sid, input.chunk()[input.chunk_pos])
                    .map_err(|_| gave_up(input.at()))?;
            }
        }
        if sid.is_tagged() {
            if sid.is_start() {
                // do nothing
            } else if sid.is_match() {
                let pattern = dfa.match_pattern(cache, sid, 0);
                // Since reverse searches report the beginning of a match
                // and the beginning is inclusive (not exclusive like the
                // end of a match), we add 1 to make it inclusive.
                mat = Some(HalfMatch::new(pattern, input.at() + 1));
                if earliest {
                    cache.search_finish(input.at());
                    return Ok(mat);
                }
            } else if sid.is_dead() {
                cache.search_finish(input.at());
                return Ok(mat);
            } else if sid.is_quit() {
                cache.search_finish(input.at());
                return Err(MatchError::quit(input.chunk()[input.chunk_pos], input.at()));
            } else {
                debug_assert!(sid.is_unknown());
                unreachable!("sid being unknown is a bug");
            }
        }
        if input.at() <= input.start() {
            break;
        }
        ensure_chunk!();
        input.chunk_pos -= 1;
    }
    cache.search_finish(input.start());
    eoi_rev(dfa, cache, input, &mut sid, &mut mat)?;
    Ok(mat)
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn init_fwd<C: Cursor>(
    dfa: &DFA,
    cache: &mut Cache,
    input: &mut Input<C>,
) -> Result<LazyStateID, MatchError> {
    let look_behind = input.ensure_look_behind();
    let start_config = start::Config::new().look_behind(look_behind).anchored(input.get_anchored());
    // let sid = dfa.start_state(&start_config)?;
    dfa.start_state(cache, &start_config).map_err(|err| match err {
        StartError::Quit { byte } => {
            let offset = input.at().checked_sub(1).expect("no quit in start without look-behind");
            MatchError::quit(byte, offset)
        }
        StartError::UnsupportedAnchored { mode } => MatchError::unsupported_anchored(mode),
        _ => panic!("damm forward compatability"),
    })
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn init_rev<C: Cursor>(
    dfa: &DFA,
    cache: &mut Cache,
    input: &mut Input<C>,
) -> Result<LazyStateID, MatchError> {
    let chunk_pos = input.chunk_pos();
    let mut look_ahead = input.chunk().get(chunk_pos).copied();
    // this branch is probably not need since chunk_pos should be in bounds
    // anyway but I would rather not make that a validity invariant
    if look_ahead.is_none() && input.advance() {
        look_ahead = input.chunk().first().copied();
        input.backtrack();
    }
    let start_config = start::Config::new().look_behind(look_ahead).anchored(input.get_anchored());
    dfa.start_state(cache, &start_config).map_err(|err| match err {
        StartError::Quit { byte } => {
            let offset =
                input.start().checked_sub(1).expect("no quit in start without look-behind");
            MatchError::quit(byte, offset)
        }
        StartError::UnsupportedAnchored { mode } => MatchError::unsupported_anchored(mode),
        _ => panic!("damm forward compatability"),
    })
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn eoi_fwd<C: Cursor>(
    dfa: &DFA,
    cache: &mut Cache,
    input: &mut Input<C>,
    sid: &mut LazyStateID,
    mat: &mut Option<HalfMatch>,
) -> Result<(), MatchError> {
    let sp = input.get_span();
    input.move_to(sp.end);
    match input.chunk().get(sp.end - input.chunk_offset()) {
        Some(&b) => {
            *sid = dfa.next_state(cache, *sid, b).map_err(|_| gave_up(sp.end))?;
            if sid.is_match() {
                let pattern = dfa.match_pattern(cache, *sid, 0);
                *mat = Some(HalfMatch::new(pattern, sp.end));
            } else if sid.is_quit() {
                return Err(MatchError::quit(b, sp.end));
            }
        }
        None => {
            *sid = dfa.next_eoi_state(cache, *sid).map_err(|_| gave_up(sp.end))?;
            if sid.is_match() {
                let pattern = dfa.match_pattern(cache, *sid, 0);
                *mat = Some(HalfMatch::new(pattern, sp.end));
            }
            // N.B. We don't have to check 'is_quit' here because the EOI
            // transition can never lead to a quit state.
            debug_assert!(!sid.is_quit());
        }
    }
    Ok(())
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn eoi_rev<C: Cursor>(
    dfa: &DFA,
    cache: &mut Cache,
    input: &mut Input<C>,
    sid: &mut LazyStateID,
    mat: &mut Option<HalfMatch>,
) -> Result<(), MatchError> {
    let sp = input.get_span();
    // debug_assert_eq!(sp.start, 0);
    if sp.start > 0 {
        input.move_to(input.start() - 1);
        let byte = input.chunk()[sp.start - input.chunk_offset() - 1];
        *sid = dfa.next_state(cache, *sid, byte).map_err(|_| gave_up(sp.start))?;
        if sid.is_match() {
            let pattern = dfa.match_pattern(cache, *sid, 0);
            *mat = Some(HalfMatch::new(pattern, sp.start));
        } else if sid.is_quit() {
            return Err(MatchError::quit(byte, sp.start - 1));
        }
    } else {
        *sid = dfa.next_eoi_state(cache, *sid).map_err(|_| gave_up(sp.start))?;
        if sid.is_match() {
            let pattern = dfa.match_pattern(cache, *sid, 0);
            *mat = Some(HalfMatch::new(pattern, 0));
        }
        // N.B. We don't have to check 'is_quit' here because the EOI
        // transition can never lead to a quit state.
        debug_assert!(!sid.is_quit());
    }
    Ok(())
}

// /// Re-compute the starting state that a DFA should be in after finding a
// /// prefilter candidate match at the position `at`.
// ///
// /// It is always correct to call this, but not always necessary. Namely,
// /// whenever the DFA has a universal start state, the DFA can remain in the
// /// start state that it was in when it ran the prefilter. Why? Because in that
// /// case, there is only one start state.
// ///
// /// When does a DFA have a universal start state? In precisely cases where
// /// it has no look-around assertions in its prefix. So for example, `\bfoo`
// /// does not have a universal start state because the start state depends on
// /// whether the byte immediately before the start position is a word byte or
// /// not. However, `foo\b` does have a universal start state because the word
// /// boundary does not appear in the pattern's prefix.
// ///
// /// So... most cases don't need this, but when a pattern doesn't have a
// /// universal start state, then after a prefilter candidate has been found, the
// /// current state *must* be re-litigated as if computing the start state at the
// /// beginning of the search because it might change. That is, not all start
// /// states are created equal.
// ///
// /// Why avoid it? Because while it's not super expensive, it isn't a trivial
// /// operation to compute the start state. It is much better to avoid it and
// /// just state in the current state if you know it to be correct.
// #[cfg_attr(feature = "perf-inline", inline(always))]
// fn prefilter_restart<'h>(
//     dfa: &DFA,
//     cache: &mut Cache,
//     input: &mut Input<'h>,
//     at: usize,
// ) -> Result<LazyStateID, MatchError> {
//     let mut input = input.clone();
//     input.set_start(at);
//     init_fwd(dfa, cache, &input)
// }

/// A convenience routine for constructing a "gave up" match error.
#[cfg_attr(feature = "perf-inline", inline(always))]
fn gave_up(offset: usize) -> MatchError {
    MatchError::gave_up(offset)
}

/// Re-compute the starting state that a DFA should be in after finding a
/// prefilter candidate match at the position `at`.
///
/// The function with the same name has a bit more docs in hybrid/search.rs.
#[cfg_attr(feature = "perf-inline", inline(always))]
fn prefilter_restart<C: Cursor>(
    dfa: &DFA,
    cache: &mut Cache,
    input: &mut Input<C>,
) -> Result<LazyStateID, MatchError> {
    init_fwd(dfa, cache, input)
}
