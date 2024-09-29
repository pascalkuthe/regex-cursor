use regex_automata::{
    dfa::{Automaton, StartError},
    util::{escape::DebugByte, prefilter::Prefilter, primitives::StateID, start},
    Anchored, HalfMatch, MatchError,
};

use crate::{cursor::Cursor, engines::dfa::accel, literal, util::empty, Input};

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
/// * The configuration of the DFA may permit it to "quit" the search.
/// For example, setting quit bytes or enabling heuristic support for
/// Unicode word boundaries. The default configuration does not enable any
/// option that could result in the DFA quitting.
/// * When the provided `Input` configuration is not supported. For
/// example, by providing an unsupported anchor mode.
///
/// When a search returns an error, callers cannot know whether a match
/// exists or not.
///
/// # Notes for implementors
///
/// Implementors of this trait are not required to implement any particular
/// match semantics (such as leftmost-first), which are instead manifest in
/// the DFA's transitions. But this search routine should behave as a
/// general "leftmost" search.
///
/// In particular, this method must continue searching even after it enters
/// a match state. The search should only terminate once it has reached
/// the end of the input or when it has entered a dead or quit state. Upon
/// termination, the position of the last byte seen while still in a match
/// state is returned.
///
/// Since this trait provides an implementation for this method by default,
/// it's unlikely that one will need to implement this.
///
/// # Example
///
/// This example shows how to use this method with a
/// [`dense::DFA`](crate::dfa::dense::DFA).
///
/// ```
/// use regex_automata::{dfa::{Automaton, dense}, HalfMatch, Input};
///
/// let dfa = dense::DFA::new("foo[0-9]+")?;
/// let expected = Some(HalfMatch::must(0, 8));
/// assert_eq!(expected, dfa.try_search_fwd(&Input::new(b"foo12345"))?);
///
/// // Even though a match is found after reading the first byte (`a`),
/// // the leftmost first match semantics demand that we find the earliest
/// // match that prefers earlier parts of the pattern over latter parts.
/// let dfa = dense::DFA::new("abc|a")?;
/// let expected = Some(HalfMatch::must(0, 3));
/// assert_eq!(expected, dfa.try_search_fwd(&Input::new(b"abc"))?);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Example: specific pattern search
///
/// This example shows how to build a multi-DFA that permits searching for
/// specific patterns.
///
/// ```
/// # if cfg!(miri) { return Ok(()); } // miri takes too long
/// use regex_automata::{
///     dfa::{Automaton, dense},
///     Anchored, HalfMatch, PatternID, Input,
/// };
///
/// let dfa = dense::Builder::new()
///     .configure(dense::Config::new().starts_for_each_pattern(true))
///     .build_many(&["[a-z0-9]{6}", "[a-z][a-z0-9]{5}"])?;
/// let haystack = "foo123".as_bytes();
///
/// // Since we are using the default leftmost-first match and both
/// // patterns match at the same starting position, only the first pattern
/// // will be returned in this case when doing a search for any of the
/// // patterns.
/// let expected = Some(HalfMatch::must(0, 6));
/// let got = dfa.try_search_fwd(&Input::new(haystack))?;
/// assert_eq!(expected, got);
///
/// // But if we want to check whether some other pattern matches, then we
/// // can provide its pattern ID.
/// let input = Input::new(haystack)
///     .anchored(Anchored::Pattern(PatternID::must(1)));
/// let expected = Some(HalfMatch::must(1, 6));
/// let got = dfa.try_search_fwd(&input)?;
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
/// use regex_automata::{dfa::{Automaton, dense}, HalfMatch, Input};
///
/// // N.B. We disable Unicode here so that we use a simple ASCII word
/// // boundary. Alternatively, we could enable heuristic support for
/// // Unicode word boundaries.
/// let dfa = dense::DFA::new(r"(?-u)\b[0-9]{3}\b")?;
/// let haystack = "foo123bar".as_bytes();
///
/// // Since we sub-slice the haystack, the search doesn't know about the
/// // larger context and assumes that `123` is surrounded by word
/// // boundaries. And of course, the match position is reported relative
/// // to the sub-slice as well, which means we get `3` instead of `6`.
/// let input = Input::new(&haystack[3..6]);
/// let expected = Some(HalfMatch::must(0, 3));
/// let got = dfa.try_search_fwd(&input)?;
/// assert_eq!(expected, got);
///
/// // But if we provide the bounds of the search within the context of the
/// // entire haystack, then the search can take the surrounding context
/// // into account. (And if we did find a match, it would be reported
/// // as a valid offset into `haystack` instead of its sub-slice.)
/// let input = Input::new(haystack).range(3..6);
/// let expected = None;
/// let got = dfa.try_search_fwd(&input)?;
/// assert_eq!(expected, got);
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[inline]
pub fn try_search_fwd<C: Cursor, A: Automaton>(
    dfa: &A,
    input: &mut Input<C>,
) -> Result<Option<HalfMatch>, MatchError> {
    let utf8empty = dfa.has_empty() && dfa.is_utf8();
    let hm = match find_fwd(dfa, input)? {
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
    empty::skip_splits_fwd(input, hm, hm.offset(), |input| {
        let got = find_fwd(dfa, input)?;
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
/// * The configuration of the DFA may permit it to "quit" the search.
/// For example, setting quit bytes or enabling heuristic support for
/// Unicode word boundaries. The default configuration does not enable any
/// option that could result in the DFA quitting.
/// * When the provided `Input` configuration is not supported. For
/// example, by providing an unsupported anchor mode.
///
/// When a search returns an error, callers cannot know whether a match
/// exists or not.
///
/// # Example
///
/// This example shows how to use this method with a
/// [`dense::DFA`](crate::dfa::dense::DFA). In particular, this
/// routine is principally useful when used in conjunction with the
/// [`nfa::thompson::Config::reverse`](crate::nfa::thompson::Config::reverse)
/// configuration. In general, it's unlikely to be correct to use
/// both `try_search_fwd` and `try_search_rev` with the same DFA since
/// any particular DFA will only support searching in one direction with
/// respect to the pattern.
///
/// ```
/// use regex_automata::{
///     nfa::thompson,
///     dfa::{Automaton, dense},
///     HalfMatch, Input,
/// };
///
/// let dfa = dense::Builder::new()
///     .thompson(thompson::Config::new().reverse(true))
///     .build("foo[0-9]+")?;
/// let expected = Some(HalfMatch::must(0, 0));
/// assert_eq!(expected, dfa.try_search_rev(&Input::new(b"foo12345"))?);
///
/// // Even though a match is found after reading the last byte (`c`),
/// // the leftmost first match semantics demand that we find the earliest
/// // match that prefers earlier parts of the pattern over latter parts.
/// let dfa = dense::Builder::new()
///     .thompson(thompson::Config::new().reverse(true))
///     .build("abc|c")?;
/// let expected = Some(HalfMatch::must(0, 0));
/// assert_eq!(expected, dfa.try_search_rev(&Input::new(b"abc"))?);
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
///     dfa::{dense::DFA, Automaton},
///     nfa::thompson,
///     HalfMatch, Input, MatchKind,
/// };
///
/// let dfa = DFA::builder()
///     .thompson(thompson::Config::new().reverse(true))
///     .build(r"")?;
///
/// // Run the reverse DFA to collect all matches.
/// let mut input = Input::new("☃");
/// let mut matches = vec![];
/// loop {
///     match dfa.try_search_rev(&input)? {
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
/// original NFA disabled (which results in disabling UTF-8 mode on the
/// DFA):
///
/// ```
/// use regex_automata::{
///     dfa::{dense::DFA, Automaton},
///     nfa::thompson,
///     HalfMatch, Input, MatchKind,
/// };
///
/// let dfa = DFA::builder()
///     .thompson(thompson::Config::new().reverse(true).utf8(false))
///     .build(r"")?;
///
/// // Run the reverse DFA to collect all matches.
/// let mut input = Input::new("☃");
/// let mut matches = vec![];
/// loop {
///     match dfa.try_search_rev(&input)? {
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
pub fn try_search_rev<C: Cursor, A: Automaton>(
    dfa: &A,
    input: &mut Input<C>,
) -> Result<Option<HalfMatch>, MatchError> {
    let utf8empty = dfa.has_empty() && dfa.is_utf8();
    let hm = match find_rev(dfa, input)? {
        None => return Ok(None),
        Some(hm) if !utf8empty => return Ok(Some(hm)),
        Some(hm) => hm,
    };
    empty::skip_splits_rev(input, hm, hm.offset(), |input| {
        let got = find_rev(dfa, input)?;
        Ok(got.map(|hm| (hm, hm.offset())))
    })
}

#[inline(never)]
pub fn find_fwd<A: Automaton + ?Sized, C: Cursor>(
    dfa: &A,
    input: &mut Input<C>,
) -> Result<Option<HalfMatch>, MatchError> {
    input.move_to(input.start());
    if input.is_done() {
        return Ok(None);
    }
    // Searching with a pattern ID is always anchored, so we should never use
    // a prefilter.
    let pre = if input.get_anchored().is_anchored() { None } else { dfa.get_prefilter() };
    if pre.is_some() {
        if input.get_earliest() {
            find_fwd_imp(dfa, input, pre, true)
        } else {
            find_fwd_imp(dfa, input, pre, false)
        }
    } else if input.get_earliest() {
        find_fwd_imp(dfa, input, None, true)
    } else {
        find_fwd_imp(dfa, input, None, false)
    }
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn find_fwd_imp<A: Automaton + ?Sized, C: Cursor>(
    dfa: &A,
    input: &mut Input<C>,
    pre: Option<&'_ Prefilter>,
    earliest: bool,
) -> Result<Option<HalfMatch>, MatchError> {
    // See 'prefilter_restart' docs for explanation.
    let universal_start = dfa.universal_start_state(Anchored::No).is_some();
    let mut mat = None;
    let mut sid = init_fwd(dfa, input)?;
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
                    sid = prefilter_restart(dfa, input)?;
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
            dfa.next_state_unchecked($sid, byte)
        }};
    }

    'outer: loop {
        // SAFETY: There are two safety invariants we need to uphold here in
        // the loops below: that 'sid' and 'prev_sid' are valid state IDs
        // for this DFA, and that 'at' is a valid index into .chunk'.
        // For the former, we rely on the invariant that next_state* and
        // start_state_forward always returns a valid state ID (given a valid
        // state ID in the former case). For the latter safety invariant, we
        // always guard unchecked access with a check that 'at' is less than
        // 'end', where 'end <=.chunk.len()'. In the unrolled loop below, we
        // ensure that 'at' is always in bounds.
        //
        // PERF: See a similar comment in src/hybrid/search.rs that justifies
        // this extra work to make the search loop fast. The same reasoning and
        // benchmarks apply here.
        let mut prev_sid;
        loop {
            if input.at() >= input.end()
                || input.chunk_pos() >= input.chunk().len() && !input.advance()
            {
                break 'outer;
            }
            prev_sid = unsafe { next_unchecked!(sid) };
            if dfa.is_special_state(prev_sid) || input.at() + 3 >= input.end() {
                core::mem::swap(&mut prev_sid, &mut sid);
                break;
            }
            input.chunk_pos += 1;
            if input.chunk_pos + 3 >= input.chunk().len() {
                core::mem::swap(&mut prev_sid, &mut sid);
                continue;
            }

            sid = unsafe { next_unchecked!(prev_sid) };
            if dfa.is_special_state(sid) {
                break;
            }
            input.chunk_pos += 1;

            prev_sid = unsafe { next_unchecked!(sid) };
            if dfa.is_special_state(prev_sid) {
                core::mem::swap(&mut prev_sid, &mut sid);
                break;
            }
            input.chunk_pos += 1;

            sid = unsafe { next_unchecked!(prev_sid) };
            if dfa.is_special_state(sid) {
                break;
            }
            input.chunk_pos += 1;
        }
        if dfa.is_special_state(sid) {
            if dfa.is_start_state(sid) {
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
                                    sid = prefilter_restart(dfa, input)?;
                                }
                                continue;
                            } else if input.at() != old_pos {
                                // the prefilter may need to do some scan ahead
                                input.move_to(old_pos);
                            }
                        }
                    }
                } else if dfa.is_accel_state(sid) {
                    let needles = dfa.accelerator(sid);
                    input.chunk_pos = accel::find_fwd(needles, input, input.chunk_pos + 1)
                        .unwrap_or_else(|| input.chunk().len());
                    continue;
                }
            } else if dfa.is_match_state(sid) {
                let pattern = dfa.match_pattern(sid, 0);
                mat = Some(HalfMatch::new(pattern, input.at()));
                if earliest {
                    return Ok(mat);
                }
                if dfa.is_accel_state(sid) {
                    let needles = dfa.accelerator(sid);
                    input.chunk_pos = accel::find_fwd(needles, input, input.chunk_pos + 1)
                        .unwrap_or_else(|| input.chunk().len());
                    continue;
                }
            } else if dfa.is_accel_state(sid) {
                let needles = dfa.accelerator(sid);
                input.chunk_pos = accel::find_fwd(needles, input, input.chunk_pos + 1)
                    .unwrap_or_else(|| input.chunk().len());
                continue;
            } else if dfa.is_dead_state(sid) {
                return Ok(mat);
            } else {
                // It's important that this is a debug_assert, since this can
                // actually be tripped even if DFA::from_bytes succeeds and
                // returns a supposedly valid DFA.
                debug_assert!(dfa.is_quit_state(sid));
                return Err(MatchError::quit(input.chunk()[input.chunk_pos], input.at()));
            }
        }
        input.chunk_pos += 1;
    }
    eoi_fwd(dfa, input, &mut sid, &mut mat)?;
    Ok(mat)
}

#[inline(never)]
pub fn find_rev<A: Automaton + ?Sized, C: Cursor>(
    dfa: &A,
    input: &mut Input<C>,
) -> Result<Option<HalfMatch>, MatchError> {
    input.move_to(input.end());
    if input.is_done() {
        return Ok(None);
    }
    if input.get_earliest() {
        find_rev_imp(dfa, input, true)
    } else {
        find_rev_imp(dfa, input, false)
    }
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn find_rev_imp<A: Automaton + ?Sized, C: Cursor>(
    dfa: &A,
    input: &mut Input<C>,
    earliest: bool,
) -> Result<Option<HalfMatch>, MatchError> {
    let mut mat = None;
    let mut sid = init_rev(dfa, input)?;
    // In reverse search, the loop below can't handle the case of searching an
    // empty slice. Ideally we could write something congruent to the forward
    // search, i.e., 'while at >= start', but 'start' might be 0. Since we use
    // an unsigned offset, 'at >= 0' is trivially always true. We could avoid
    // this extra case handling by using a signed offset, but Rust makes it
    // annoying to do. So... We just handle the empty case separately.
    if input.start() == input.end() || input.chunk_pos == 0 && !input.backtrack() {
        eoi_rev(dfa, input, &mut sid, &mut mat)?;
        return Ok(mat);
    }
    input.chunk_pos -= 1;

    // This could just be a closure, but then I think it would be unsound
    // because it would need to be safe to invoke. This way, the lack of safety
    // is clearer in the code below.
    macro_rules! next_unchecked {
        ($sid:expr) => {{
            let byte = *input.chunk().get_unchecked(input.chunk_pos);
            dfa.next_state_unchecked($sid, byte)
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

    loop {
        // SAFETY: See comments in 'find_fwd' for a safety argument.
        let mut prev_sid;
        while input.at() >= input.start() {
            prev_sid = unsafe { next_unchecked!(sid) };
            if dfa.is_special_state(prev_sid) || input.at() <= input.start().saturating_add(3) {
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
            if dfa.is_special_state(sid) {
                break;
            }
            input.chunk_pos -= 1;

            prev_sid = unsafe { next_unchecked!(sid) };
            if dfa.is_special_state(prev_sid) {
                core::mem::swap(&mut prev_sid, &mut sid);
                break;
            }
            input.chunk_pos -= 1;

            sid = unsafe { next_unchecked!(prev_sid) };
            if dfa.is_special_state(sid) {
                break;
            }
            input.chunk_pos -= 1;
        }
        if dfa.is_special_state(sid) {
            if dfa.is_start_state(sid) {
                if dfa.is_accel_state(sid) {
                    let needles = dfa.accelerator(sid);
                    input.chunk_pos = accel::find_rev(needles, input, input.chunk_pos)
                        .map(|i| i + 1)
                        .unwrap_or(0);
                }
            } else if dfa.is_match_state(sid) {
                let pattern = dfa.match_pattern(sid, 0);
                // Since reverse searches report the beginning of a match
                // and the beginning is inclusive (not exclusive like the
                // end of a match), we add 1 to make it inclusive.
                mat = Some(HalfMatch::new(pattern, input.at() + 1));
                if earliest {
                    return Ok(mat);
                }
                if dfa.is_accel_state(sid) {
                    let needles = dfa.accelerator(sid);
                    input.chunk_pos = accel::find_rev(needles, input, input.chunk_pos)
                        .map(|i| i + 1)
                        .unwrap_or(0);
                }
            } else if dfa.is_accel_state(sid) {
                let needles = dfa.accelerator(sid);
                // If the accelerator returns nothing, why don't we quit the
                // search? Well, if the accelerator doesn't find anything, that
                // doesn't mean we don't have a match. It just means that we
                // can't leave the current state given one of the 255 possible
                // byte values. However, there might be an EOI transition. So
                // we set 'at' to the end of the.chunk, which will cause
                // this loop to stop and fall down into the EOI transition.
                input.chunk_pos =
                    accel::find_rev(needles, input, input.chunk_pos).map(|i| i + 1).unwrap_or(0);
            } else if dfa.is_dead_state(sid) {
                return Ok(mat);
            } else {
                debug_assert!(dfa.is_quit_state(sid));
                return Err(MatchError::quit(input.chunk()[input.chunk_pos], input.at()));
            }
        }
        if input.at() <= input.start() {
            break;
        }
        ensure_chunk!();
        input.chunk_pos -= 1;
    }
    eoi_rev(dfa, input, &mut sid, &mut mat)?;
    Ok(mat)
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn init_fwd<A: Automaton + ?Sized, C: Cursor>(
    dfa: &A,
    input: &mut Input<C>,
) -> Result<StateID, MatchError> {
    let look_behind = input.ensure_look_behind();
    let start_config = start::Config::new().look_behind(look_behind).anchored(input.get_anchored());
    // let sid = dfa.start_state(&start_config)?;
    dfa.start_state(&start_config).map_err(|err| match err {
        StartError::Quit { byte } => {
            let offset = input.at().checked_sub(1).expect("no quit in start without look-behind");
            MatchError::quit(byte, offset)
        }
        StartError::UnsupportedAnchored { mode } => MatchError::unsupported_anchored(mode),
        _ => panic!("damm forward compatability"),
    })
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn init_rev<A: Automaton + ?Sized, C: Cursor>(
    dfa: &A,
    input: &mut Input<C>,
) -> Result<StateID, MatchError> {
    let chunk_pos = input.chunk_pos();
    let mut look_ahead = input.chunk().get(chunk_pos).copied();
    // this branch is probably not need since chunk_pos should be in bounds
    // anyway but I would rather not make that a validity invariant
    if chunk_pos + input.chunk_offset() == input.slice_span.end {
        look_ahead = None
    } else if look_ahead.is_none() && input.advance() {
        look_ahead = input.chunk().first().copied();
        input.backtrack();
    }
    let start_config = start::Config::new().look_behind(look_ahead).anchored(input.get_anchored());
    dfa.start_state(&start_config).map_err(|err| match err {
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
fn eoi_fwd<A: Automaton + ?Sized, C: Cursor>(
    dfa: &A,
    input: &mut Input<C>,
    sid: &mut StateID,
    mat: &mut Option<HalfMatch>,
) -> Result<(), MatchError> {
    let sp = input.get_span();
    input.move_to(sp.end);
    match input.chunk().get(sp.end - input.chunk_offset()) {
        Some(&b) if sp.end != input.slice_span.end => {
            *sid = dfa.next_state(*sid, b);
            if dfa.is_match_state(*sid) {
                let pattern = dfa.match_pattern(*sid, 0);
                *mat = Some(HalfMatch::new(pattern, sp.end));
            } else if dfa.is_quit_state(*sid) {
                return Err(MatchError::quit(b, sp.end));
            }
        }
        _ => {
            *sid = dfa.next_eoi_state(*sid);
            if dfa.is_match_state(*sid) {
                let pattern = dfa.match_pattern(*sid, 0);
                *mat = Some(HalfMatch::new(pattern, sp.end));
            }
            // N.B. We don't have to check 'is_quit' here because the EOI
            // transition can never lead to a quit state.
            debug_assert!(!dfa.is_quit_state(*sid));
        }
    }
    Ok(())
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn eoi_rev<A: Automaton + ?Sized, C: Cursor>(
    dfa: &A,
    input: &mut Input<C>,
    sid: &mut StateID,
    mat: &mut Option<HalfMatch>,
) -> Result<(), MatchError> {
    let sp = input.get_span();
    if sp.start > input.slice_span.start {
        input.move_to(input.start() - 1);
        let byte = input.chunk()[sp.start - input.chunk_offset() - 1];
        *sid = dfa.next_state(*sid, byte);
        if dfa.is_match_state(*sid) {
            let pattern = dfa.match_pattern(*sid, 0);
            *mat = Some(HalfMatch::new(pattern, sp.start));
        } else if dfa.is_quit_state(*sid) {
            return Err(MatchError::quit(byte, sp.start - 1));
        }
    } else {
        *sid = dfa.next_eoi_state(*sid);
        if dfa.is_match_state(*sid) {
            let pattern = dfa.match_pattern(*sid, 0);
            *mat = Some(HalfMatch::new(pattern, 0));
        }
        // N.B. We don't have to check 'is_quit' here because the EOI
        // transition can never lead to a quit state.
        debug_assert!(!dfa.is_quit_state(*sid));
    }
    Ok(())
}

/// Re-compute the starting state that a DFA should be in after finding a
/// prefilter candidate match at the position `at`.
///
/// The function with the same name has a bit more docs in hybrid/search.rs.
#[cfg_attr(feature = "perf-inline", inline(always))]
fn prefilter_restart<A: Automaton + ?Sized, C: Cursor>(
    dfa: &A,
    input: &mut Input<C>,
) -> Result<StateID, MatchError> {
    init_fwd(dfa, input)
}
