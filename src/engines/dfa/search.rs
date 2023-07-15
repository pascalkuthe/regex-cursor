use regex_automata::{
    dfa::Automaton,
    util::{prefilter::Prefilter, primitives::StateID},
    Anchored, HalfMatch, MatchError,
};

use crate::{engines::dfa::accel, Input};

#[inline(never)]
pub fn find_fwd<A: Automaton + ?Sized>(
    dfa: &A,
    input: &mut Input<'_>,
) -> Result<Option<HalfMatch>, MatchError> {
    if input.is_done() {
        return Ok(None);
    }
    let pre = if input.get_anchored().is_anchored() { None } else { dfa.get_prefilter() };
    // Searching with a pattern ID is always anchored, so we should never use
    // a prefilter.
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
fn find_fwd_imp<A: Automaton + ?Sized>(
    dfa: &A,
    input: &mut Input<'_>,
    pre: Option<&'_ Prefilter>,
    earliest: bool,
) -> Result<Option<HalfMatch>, MatchError> {
    // See 'prefilter_restart' docs for explanation.
    let universal_start = dfa.universal_start_state(Anchored::No).is_some();
    let mut mat = None;
    let (mut chunk_at, mut sid) = init_fwd(dfa, input)?;

    // This could just be a closure, but then I think it would be unsound
    // because it would need to be safe to invoke. This way, the lack of safety
    // is clearer in the code below.
    macro_rules! next_unchecked {
        ($sid:expr) => {{
            debug_assert!(chunk_at < input.haystack().len());
            let byte = *input.haystack().get_unchecked(chunk_at);
            dfa.next_state_unchecked($sid, byte)
        }};
    }
    macro_rules! at {
        () => {
            input.haystack_off() + chunk_at
        };
    }
    #[rustfmt::skip]
    macro_rules! ensure_chunk {
        () => {
            if chunk_at >= input.haystack().len() {
                debug_assert_eq!(chunk_at, input.haystack().len());
                chunk_at = 0;
                input.advance_fwd();
            }
        };
    }

    // if let Some(ref pre) = pre {
    //     let span = Span::from(at..input.end());
    //     // If a prefilter doesn't report false positives, then we don't need to
    //     // touch the DFA at all. However, since all matches include the pattern
    //     // ID, and the prefilter infrastructure doesn't report pattern IDs, we
    //     // limit this optimization to cases where there is exactly one pattern.
    //     // In that case, any match must be the 0th pattern.
    //     match pre.find(input.haystack(), span) {
    //         None => return Ok(mat),
    //         Some(ref span) => {
    //             at = span.start;
    //             if !universal_start {
    //                 sid = prefilter_restart(dfa, &input, at)?;
    //             }
    //         }
    //     }
    // }
    while at!() < input.end() {
        // SAFETY: There are two safety invariants we need to uphold here in
        // the loops below: that 'sid' and 'prev_sid' are valid state IDs
        // for this DFA, and that 'at' is a valid index into 'haystack'.
        // For the former, we rely on the invariant that next_state* and
        // start_state_forward always returns a valid state ID (given a valid
        // state ID in the former case). For the latter safety invariant, we
        // always guard unchecked access with a check that 'at' is less than
        // 'end', where 'end <= haystack.len()'. In the unrolled loop below, we
        // ensure that 'at' is always in bounds.
        //
        // PERF: See a similar comment in src/hybrid/search.rs that justifies
        // this extra work to make the search loop fast. The same reasoning and
        // benchmarks apply here.
        let mut prev_sid;
        while at!() < input.end() {
            ensure_chunk!();
            prev_sid = unsafe { next_unchecked!(sid) };
            if dfa.is_special_state(prev_sid) || at!() + 3 >= input.end() {
                core::mem::swap(&mut prev_sid, &mut sid);
                break;
            }
            chunk_at += 1;
            // this is a bit of a weird one... we could just break out of the loop same as above and be done
            // with it and avoid the extra branch in the hot loop
            if chunk_at + 3 >= input.haystack().len() {
                core::mem::swap(&mut prev_sid, &mut sid);
                continue;
            }

            sid = unsafe { next_unchecked!(prev_sid) };
            if dfa.is_special_state(sid) {
                break;
            }
            chunk_at += 1;

            prev_sid = unsafe { next_unchecked!(sid) };
            if dfa.is_special_state(prev_sid) {
                core::mem::swap(&mut prev_sid, &mut sid);
                break;
            }
            chunk_at += 1;

            sid = unsafe { next_unchecked!(prev_sid) };
            if dfa.is_special_state(sid) {
                break;
            }
            chunk_at += 1;
        }
        if dfa.is_special_state(sid) {
            if dfa.is_start_state(sid) {
                if let Some(ref pre) = pre {
                    // let span = Span::from(at!()..input.end());
                    // match pre.find(input, span) {
                    //     None => return Ok(mat),
                    //     Some(ref span) => {
                    //         // We want to skip any update to 'at' below
                    //         // at the end of this iteration and just
                    //         // jump immediately back to the next state
                    //         // transition at the leading position of the
                    //         // candidate match.
                    //         //
                    //         // ... but only if we actually made progress
                    //         // with our prefilter, otherwise if the start
                    //         // state has a self-loop, we can get stuck.
                    //         if span.start > at!() {
                    //             chunk_at = input.move_to(span.start).unwrap();
                    //             if !universal_start {
                    //                 sid = prefilter_restart(dfa, &input, at!())?;
                    //             }
                    //             continue;
                    //         }
                    //     }
                    // }
                } else if dfa.is_accel_state(sid) {
                    let needles = dfa.accelerator(sid);
                    chunk_at = accel::find_fwd(needles, input, chunk_at + 1)
                        .unwrap_or_else(|| input.haystack().len());
                    continue;
                }
            } else if dfa.is_match_state(sid) {
                let pattern = dfa.match_pattern(sid, 0);
                mat = Some(HalfMatch::new(pattern, at!()));
                if earliest {
                    return Ok(mat);
                }
                if dfa.is_accel_state(sid) {
                    let needles = dfa.accelerator(sid);
                    chunk_at = accel::find_fwd(needles, input, chunk_at + 1)
                        .unwrap_or_else(|| input.haystack().len());
                    continue;
                }
            } else if dfa.is_accel_state(sid) {
                let needles = dfa.accelerator(sid);
                chunk_at = accel::find_fwd(needles, input, chunk_at + 1)
                    .unwrap_or_else(|| input.haystack().len());
                continue;
            } else if dfa.is_dead_state(sid) {
                return Ok(mat);
            } else {
                // It's important that this is a debug_assert, since this can
                // actually be tripped even if DFA::from_bytes succeeds and
                // returns a supposedly valid DFA.
                debug_assert!(dfa.is_quit_state(sid));
                return Err(MatchError::quit(input.haystack()[chunk_at], at!()));
            }
        }
        chunk_at += 1;
    }
    eoi_fwd(dfa, input, &mut sid, &mut mat)?;
    Ok(mat)
}

#[inline(never)]
pub fn find_rev<A: Automaton + ?Sized>(
    dfa: &A,
    input: &mut Input<'_>,
) -> Result<Option<HalfMatch>, MatchError> {
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
fn find_rev_imp<A: Automaton + ?Sized>(
    dfa: &A,
    input: &mut Input<'_>,
    earliest: bool,
) -> Result<Option<HalfMatch>, MatchError> {
    let mut mat = None;
    let (mut chunk_at, mut sid) = init_rev(dfa, input)?;
    // In reverse search, the loop below can't handle the case of searching an
    // empty slice. Ideally we could write something congruent to the forward
    // search, i.e., 'while at >= start', but 'start' might be 0. Since we use
    // an unsigned offset, 'at >= 0' is trivially always true. We could avoid
    // this extra case handling by using a signed offset, but Rust makes it
    // annoying to do. So... We just handle the empty case separately.
    if input.start() == input.end() {
        eoi_rev(dfa, input, &mut sid, &mut mat)?;
        return Ok(mat);
    }

    // This could just be a closure, but then I think it would be unsound
    // because it would need to be safe to invoke. This way, the lack of safety
    // is clearer in the code below.
    macro_rules! next_unchecked {
        ($sid:expr) => {{
            let byte = *input.haystack().get_unchecked(chunk_at);
            dfa.next_state_unchecked($sid, byte)
        }};
    }
    macro_rules! at {
        () => {
            input.haystack_off() + chunk_at
        };
    }
    #[rustfmt::skip]
    macro_rules! ensure_in_chunk {
        () => {
            if chunk_at == 0 {
                let Some(new_chunk) = input.advance_rev() else{
                    break;
                };
                chunk_at = new_chunk.len() - 1;
            }
        };
    }
    loop {
        // SAFETY: See comments in 'find_fwd' for a safety argument.
        let mut prev_sid;
        while at!() >= input.start() {
            prev_sid = unsafe { next_unchecked!(sid) };
            if dfa.is_special_state(prev_sid) || at!() <= input.start().saturating_add(3) {
                core::mem::swap(&mut prev_sid, &mut sid);
                break;
            }
            chunk_at -= 1;
            if chunk_at <= 2 {
                core::mem::swap(&mut prev_sid, &mut sid);
                ensure_in_chunk!();
                continue;
            }

            sid = unsafe { next_unchecked!(prev_sid) };
            if dfa.is_special_state(sid) {
                break;
            }
            chunk_at -= 1;

            prev_sid = unsafe { next_unchecked!(sid) };
            if dfa.is_special_state(prev_sid) {
                core::mem::swap(&mut prev_sid, &mut sid);
                break;
            }
            chunk_at -= 1;

            sid = unsafe { next_unchecked!(prev_sid) };
            if dfa.is_special_state(sid) {
                break;
            }
            chunk_at -= 1;
            ensure_in_chunk!();
        }
        if dfa.is_special_state(sid) {
            if dfa.is_start_state(sid) {
                if dfa.is_accel_state(sid) {
                    let needles = dfa.accelerator(sid);
                    chunk_at =
                        accel::find_rev(needles, input, chunk_at).map(|i| i + 1).unwrap_or(0);
                }
            } else if dfa.is_match_state(sid) {
                let pattern = dfa.match_pattern(sid, 0);
                // Since reverse searches report the beginning of a match
                // and the beginning is inclusive (not exclusive like the
                // end of a match), we add 1 to make it inclusive.
                mat = Some(HalfMatch::new(pattern, at!() + 1));
                if earliest {
                    return Ok(mat);
                }
                if dfa.is_accel_state(sid) {
                    let needles = dfa.accelerator(sid);
                    chunk_at =
                        accel::find_rev(needles, input, chunk_at).map(|i| i + 1).unwrap_or(0);
                }
            } else if dfa.is_accel_state(sid) {
                let needles = dfa.accelerator(sid);
                // If the accelerator returns nothing, why don't we quit the
                // search? Well, if the accelerator doesn't find anything, that
                // doesn't mean we don't have a match. It just means that we
                // can't leave the current state given one of the 255 possible
                // byte values. However, there might be an EOI transition. So
                // we set 'at' to the end of the haystack, which will cause
                // this loop to stop and fall down into the EOI transition.
                chunk_at = accel::find_rev(needles, input, chunk_at).map(|i| i + 1).unwrap_or(0);
            } else if dfa.is_dead_state(sid) {
                return Ok(mat);
            } else {
                debug_assert!(dfa.is_quit_state(sid));
                return Err(MatchError::quit(input.haystack()[chunk_at], at!()));
            }
        }
        if chunk_at <= input.start() {
            break;
        }
        chunk_at -= 1;
    }
    eoi_rev(dfa, input, &mut sid, &mut mat)?;
    Ok(mat)
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn init_fwd<A: Automaton + ?Sized>(
    dfa: &A,
    input: &mut Input<'_>,
) -> Result<(usize, StateID), MatchError> {
    let sid =
        dfa.start_state_forward_with(input.get_anchored(), input.look_behind(), input.get_span())?;
    // Start states can never be match states, since all matches are delayed
    // by 1 byte.
    debug_assert!(!dfa.is_match_state(sid));
    let start = input.move_to(input.start()).unwrap_or_default();
    Ok((start, sid))
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn init_rev<A: Automaton + ?Sized>(
    dfa: &A,
    input: &mut Input<'_>,
) -> Result<(usize, StateID), MatchError> {
    let sid =
        dfa.start_state_reverse_with(input.get_anchored(), input.look_ahead(), input.get_span())?;
    // Start states can never be match states, since all matches are delayed
    // by 1 byte.
    debug_assert!(!dfa.is_match_state(sid));
    let start = input.move_to(input.end() - 1).unwrap_or_default();
    Ok((start, sid))
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn eoi_fwd<A: Automaton + ?Sized>(
    dfa: &A,
    input: &Input<'_>,
    sid: &mut StateID,
    mat: &mut Option<HalfMatch>,
) -> Result<(), MatchError> {
    let sp = input.get_span();
    match input.haystack().get(sp.end) {
        Some(&b) => {
            *sid = dfa.next_state(*sid, b);
            if dfa.is_match_state(*sid) {
                let pattern = dfa.match_pattern(*sid, 0);
                *mat = Some(HalfMatch::new(pattern, sp.end));
            } else if dfa.is_quit_state(*sid) {
                return Err(MatchError::quit(b, sp.end));
            }
        }
        None => {
            *sid = dfa.next_eoi_state(*sid);
            if dfa.is_match_state(*sid) {
                let pattern = dfa.match_pattern(*sid, 0);
                *mat = Some(HalfMatch::new(pattern, input.haystack().len()));
            }
            // N.B. We don't have to check 'is_quit' here because the EOI
            // transition can never lead to a quit state.
            debug_assert!(!dfa.is_quit_state(*sid));
        }
    }
    Ok(())
}

#[cfg_attr(feature = "perf-inline", inline(always))]
fn eoi_rev<A: Automaton + ?Sized>(
    dfa: &A,
    input: &Input<'_>,
    sid: &mut StateID,
    mat: &mut Option<HalfMatch>,
) -> Result<(), MatchError> {
    let sp = input.get_span();
    if sp.start > 0 {
        let byte = input.haystack()[sp.start - 1];
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

// /// Re-compute the starting state that a DFA should be in after finding a
// /// prefilter candidate match at the position `at`.
// ///
// /// The function with the same name has a bit more docs in hybrid/search.rs.
// #[cfg_attr(feature = "perf-inline", inline(always))]
// fn prefilter_restart<A: Automaton + ?Sized>(
//     dfa: &A,
//     input: &Input<'_>,
//     at: usize,
// ) -> Result<StateID, MatchError> {
//     let mut input = input.clone();
//     input.set_start(at);
//     init_fwd(dfa, &input)
// }
