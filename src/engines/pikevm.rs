#[cfg(feature = "internal-instrument-pikevm")]
use core::cell::RefCell;

pub use regex_automata::nfa::thompson::pikevm::PikeVM;
use regex_automata::nfa::thompson::State;
use regex_automata::util::captures::Captures;
use regex_automata::util::primitives::{NonMaxUsize, SmallIndex, StateID};
use regex_automata::{Anchored, HalfMatch, Match, MatchKind, PatternID};

use crate::cursor::Cursor;
use crate::util::sparse_set::SparseSet;
use crate::util::{empty, iter};
use crate::{literal, Input};

#[cfg(test)]
mod tests;

/// Returns an iterator over all non-overlapping leftmost matches in the
/// given bytes. If no match exists, then the iterator yields no elements.
///
/// # Example
///
/// ```
/// use regex_automata::{nfa::thompson::pikevm::PikeVM, Match};
///
/// let re = PikeVM::new("foo[0-9]+")?;
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
pub fn find_iter<'r, 'c, C: Cursor>(
    vm: &'r PikeVM,
    cache: &'c mut Cache,
    input: Input<C>,
) -> FindMatches<'r, 'c, C> {
    let caps = Captures::matches(vm.get_nfa().group_info().clone());
    let it = iter::Searcher::new(input.into());
    FindMatches { re: vm, cache, caps, it }
}

/// Executes a leftmost forward search and writes the spans of capturing
/// groups that participated in a match into the provided [`Captures`]
/// value. If no match was found, then [`Captures::is_match`] is guaranteed
/// to return `false`.
///
/// This is like [`PikeVM::captures`], but it accepts a concrete `&Input`
/// instead of an `Into<Input>`.
///
/// # Example: specific pattern search
///
/// This example shows how to build a multi-PikeVM that permits searching
/// for specific patterns.
///
/// ```
/// use regex_automata::{
///     nfa::thompson::pikevm::PikeVM,
///     Anchored, Match, PatternID, Input,
/// };
///
/// let re = PikeVM::new_many(&["[a-z0-9]{6}", "[a-z][a-z0-9]{5}"])?;
/// let (mut cache, mut caps) = (re.create_cache(), re.create_captures());
/// let haystack = "foo123";
///
/// // Since we are using the default leftmost-first match and both
/// // patterns match at the same starting position, only the first pattern
/// // will be returned in this case when doing a search for any of the
/// // patterns.
/// let expected = Some(Match::must(0, 0..6));
/// re.search(&mut cache, &Input::new(haystack), &mut caps);
/// assert_eq!(expected, caps.get_match());
///
/// // But if we want to check whether some other pattern matches, then we
/// // can provide its pattern ID.
/// let expected = Some(Match::must(1, 0..6));
/// let input = Input::new(haystack)
///     .anchored(Anchored::Pattern(PatternID::must(1)));
/// re.search(&mut cache, &input, &mut caps);
/// assert_eq!(expected, caps.get_match());
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
/// # if cfg!(miri) { return Ok(()); } // miri takes too long
/// use regex_automata::{nfa::thompson::pikevm::PikeVM, Match, Input};
///
/// let re = PikeVM::new(r"\b[0-9]{3}\b")?;
/// let (mut cache, mut caps) = (re.create_cache(), re.create_captures());
/// let haystack = "foo123bar";
///
/// // Since we sub-slice the haystack, the search doesn't know about
/// // the larger context and assumes that `123` is surrounded by word
/// // boundaries. And of course, the match position is reported relative
/// // to the sub-slice as well, which means we get `0..3` instead of
/// // `3..6`.
/// let expected = Some(Match::must(0, 0..3));
/// re.search(&mut cache, &Input::new(&haystack[3..6]), &mut caps);
/// assert_eq!(expected, caps.get_match());
///
/// // But if we provide the bounds of the search within the context of the
/// // entire haystack, then the search can take the surrounding context
/// // into account. (And if we did find a match, it would be reported
/// // as a valid offset into `haystack` instead of its sub-slice.)
/// let expected = None;
/// let input = Input::new(haystack).range(3..6);
/// re.search(&mut cache, &input, &mut caps);
/// assert_eq!(expected, caps.get_match());
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[inline]
pub fn search<C: Cursor>(
    vm: &PikeVM,
    cache: &mut Cache,
    input: &mut Input<C>,
    caps: &mut Captures,
) {
    caps.set_pattern(None);
    let pid = search_slots(vm, cache, input, caps.slots_mut());
    caps.set_pattern(pid);
}
/// A simple macro for conditionally executing instrumentation logic when
/// the 'trace' log level is enabled. This is a compile-time no-op when the
/// 'internal-instrument-pikevm' feature isn't enabled. The intent here is that
/// this makes it easier to avoid doing extra work when instrumentation isn't
/// enabled.
///
/// This macro accepts a closure of type `|&mut Counters|`. The closure can
/// then increment counters (or whatever) in accordance with what one wants
/// to track.
macro_rules! instrument {
    ($fun:expr) => {
        #[cfg(feature = "internal-instrument-pikevm")]
        {
            let fun: &mut dyn FnMut(&mut Counters) = &mut $fun;
            COUNTERS.with(|c: &RefCell<Counters>| fun(&mut *c.borrow_mut()));
        }
    };
}

#[cfg(feature = "internal-instrument-pikevm")]
std::thread_local! {
    /// Effectively global state used to keep track of instrumentation
    /// counters. The "proper" way to do this is to thread it through the
    /// PikeVM, but it makes the code quite icky. Since this is just a
    /// debugging feature, we're content to relegate it to thread local
    /// state. When instrumentation is enabled, the counters are reset at the
    /// beginning of every search and printed (with the 'trace' log level) at
    /// the end of every search.
    static COUNTERS: RefCell<Counters> = RefCell::new(Counters::empty());
}

pub fn search_slots<C: Cursor>(
    vm: &PikeVM,
    cache: &mut Cache,
    input: &mut Input<C>,
    slots: &mut [Option<NonMaxUsize>],
) -> Option<PatternID> {
    let utf8empty = vm.get_nfa().has_empty() && vm.get_nfa().is_utf8();
    if !utf8empty {
        let hm = search_slots_imp(vm, cache, input, slots)?;
        return Some(hm.pattern());
    }
    // There is an unfortunate special case where if the regex can
    // match the empty string and UTF-8 mode is enabled, the search
    // implementation requires that the slots have at least as much space
    // to report the bounds of any match. This is so zero-width matches
    // that split a codepoint can be filtered out.
    //
    // Note that if utf8empty is true, we specialize the case for when
    // the number of patterns is 1. In that case, we can just use a stack
    // allocation. Otherwise we resort to a heap allocation, which we
    // convince ourselves we're fine with due to the pathological nature of
    // this case.
    let min = vm.get_nfa().group_info().implicit_slot_len();
    if slots.len() >= min {
        let hm = search_slots_imp(vm, cache, input, slots)?;
        return Some(hm.pattern());
    }
    if vm.get_nfa().pattern_len() == 1 {
        let mut enough = [None, None];
        let got = search_slots_imp(vm, cache, input, &mut enough);
        // This is OK because we know `enough` is strictly bigger than
        // `slots`, otherwise this special case isn't reached.
        slots.copy_from_slice(&enough[..slots.len()]);
        return got.map(|hm| hm.pattern());
    }
    let mut enough = vec![None; min];
    let got = search_slots_imp(vm, cache, input, &mut enough);
    // This is OK because we know `enough` is strictly bigger than `slots`,
    // otherwise this special case isn't reached.
    slots.copy_from_slice(&enough[..slots.len()]);
    got.map(|hm| hm.pattern())
}

/// This is the actual implementation of `search_slots_imp` that
/// doesn't account for the special case when 1) the NFA has UTF-8 mode
/// enabled, 2) the NFA can match the empty string and 3) the caller has
/// provided an insufficient number of slots to record match offsets.
#[inline(never)]
fn search_slots_imp<C: Cursor>(
    vm: &PikeVM,
    cache: &mut Cache,
    input: &mut Input<C>,
    slots: &mut [Option<NonMaxUsize>],
) -> Option<HalfMatch> {
    let utf8empty = vm.get_nfa().has_empty() && vm.get_nfa().is_utf8();
    let hm = match search_imp(vm, cache, input, slots) {
        None => return None,
        Some(hm) if !utf8empty => return Some(hm),
        Some(hm) => hm,
    };
    empty::skip_splits_fwd(input, hm, hm.offset(), |input| {
        Ok(search_imp(vm, cache, input, slots).map(|hm| (hm, hm.offset())))
    })
    // OK because the PikeVM never errors.
    .unwrap()
}

/// Return the starting configuration of a PikeVM search.
///
/// The "start config" is basically whether the search should be anchored
/// or not and the NFA state ID at which to begin the search. The state ID
/// returned always corresponds to an anchored starting state even when the
/// search is unanchored. This is because the PikeVM search loop deals with
/// unanchored searches with an explicit epsilon closure out of the start
/// state.
///
/// This routine accounts for both the caller's `Input` configuration
/// and the pattern itself. For example, even if the caller asks for an
/// unanchored search, if the pattern itself is anchored, then this will
/// always return 'true' because implementing an unanchored search in that
/// case would be incorrect.
///
/// Similarly, if the caller requests an anchored search for a particular
/// pattern, then the starting state ID returned will reflect that.
///
/// If a pattern ID is given in the input configuration that is not in
/// this regex, then `None` is returned.
fn start_config<C: Cursor>(vm: &PikeVM, input: &Input<C>) -> Option<(bool, StateID)> {
    match input.get_anchored() {
        // Only way we're unanchored is if both the caller asked for an
        // unanchored search *and* the pattern is itself not anchored.
        Anchored::No => {
            Some((vm.get_nfa().is_always_start_anchored(), vm.get_nfa().start_anchored()))
        }
        Anchored::Yes => Some((true, vm.get_nfa().start_anchored())),
        Anchored::Pattern(pid) => Some((true, vm.get_nfa().start_pattern(pid)?)),
    }
}

fn search_imp<C: Cursor>(
    vm: &PikeVM,
    cache: &mut Cache,
    input: &mut Input<C>,
    slots: &mut [Option<NonMaxUsize>],
) -> Option<HalfMatch> {
    cache.setup_search(slots.len());
    if input.is_done() {
        return None;
    }
    instrument!(|c| c.reset(&self.nfa));

    // Whether we want to visit all match states instead of emulating the
    // 'leftmost' semantics of typical backtracking regex engines.
    let allmatches = vm.get_config().get_match_kind() == MatchKind::All;
    let (anchored, start_id) = match start_config(vm, input) {
        None => return None,
        Some(config) => config,
    };

    let pre = if anchored { None } else { vm.get_config().get_prefilter() };
    let Cache { ref mut stack, ref mut curr, ref mut next } = cache;
    let mut hm = None;
    // Yes, our search doesn't end at input.end(), but includes it. This
    // is necessary because matches are delayed by one byte, just like
    // how the DFA engines work. The delay is used to handle look-behind
    // assertions. In the case of the PikeVM, the delay is implemented
    // by not considering a match to exist until it is visited in
    // 'steps'. Technically, we know a match exists in the previous
    // iteration via 'epsilon_closure'. (It's the same thing in NFA-to-DFA
    // determinization. We don't mark a DFA state as a match state if it
    // contains an NFA match state, but rather, whether the DFA state was
    // generated by a transition from a DFA state that contains an NFA
    // match state.)
    input.move_to(input.start());
    input.clear_look_behind();
    input.ensure_look_behind();
    while input.at() <= input.end() {
        // If we have no states left to visit, then there are some cases
        // where we know we can quit early or even skip ahead.
        if curr.set.is_empty() {
            // We have a match and we haven't been instructed to continue
            // on even after finding a match, so we can quit.
            if hm.is_some() && !allmatches {
                break;
            }
            // If we're running an anchored search and we've advanced
            // beyond the start position with no other states to try, then
            // we will never observe a match and thus can stop.
            if anchored && input.at() > input.start() {
                break;
            }
            // If there no states left to explore at this position and we
            // know we can't terminate early, then we are effectively at
            // the starting state of the NFA. If we fell through here,
            // we'd end up adding our '(?s-u:.)*?' prefix and it would be
            // the only thing in 'curr'. So we might as well just skip
            // ahead until we find something that we know might advance us
            // forward.
            if let Some(pre) = pre {
                match literal::find(pre, input) {
                    None => break,
                    Some(ref span) => {
                        input.move_to(span.start);
                    }
                }
            }
        }
        // Instead of using the NFA's unanchored start state, we actually
        // always use its anchored starting state. As a result, when doing
        // an unanchored search, we need to simulate our own '(?s-u:.)*?'
        // prefix, to permit a match to appear anywhere.
        //
        // Now, we don't *have* to do things this way. We could use the
        // NFA's unanchored starting state and do one 'epsilon_closure'
        // call from that starting state before the main loop here. And
        // that is just as correct. However, it turns out to be slower
        // than our approach here because it slightly increases the cost
        // of processing each byte by requiring us to visit more NFA
        // states to deal with the additional NFA states in the unanchored
        // prefix. By simulating it explicitly here, we lower those costs
        // substantially. The cost is itself small, but it adds up for
        // large haystacks.
        //
        // In order to simulate the '(?s-u:.)*?' prefix---which is not
        // greedy---we are careful not to perform an epsilon closure on
        // the start state if we already have a match. Namely, if we
        // did otherwise, we would never reach a terminating condition
        // because there would always be additional states to process.
        // In effect, the exclusion of running 'epsilon_closure' when
        // we have a match corresponds to the "dead" states we have in
        // our DFA regex engines. Namely, in a DFA, match states merely
        // instruct the search execution to record the current offset as
        // the most recently seen match. It is the dead state that actually
        // indicates when to stop the search (other than EOF or quit
        // states).
        //
        // However, when 'allmatches' is true, the caller has asked us to
        // leave in every possible match state. This tends not to make a
        // whole lot of sense in unanchored searches, because it means the
        // search really cannot terminate until EOF. And often, in that
        // case, you wind up skipping over a bunch of matches and are left
        // with the "last" match. Arguably, it just doesn't make a lot of
        // sense to run a 'leftmost' search (which is what this routine is)
        // with 'allmatches' set to true. But the DFAs support it and this
        // matches their behavior. (Generally, 'allmatches' is useful for
        // overlapping searches or leftmost anchored searches to find the
        // longest possible match by ignoring match priority.)
        //
        // Additionally, when we're running an anchored search, this
        // epsilon closure should only be computed at the beginning of the
        // search. If we re-computed it at every position, we would be
        // simulating an unanchored search when we were tasked to perform
        // an anchored search.
        if (!hm.is_some() || allmatches) && (!anchored || input.at() == input.start()) {
            // Since we are adding to the 'curr' active states and since
            // this is for the start ID, we use a slots slice that is
            // guaranteed to have the right length but where every element
            // is absent. This is exactly what we want, because this
            // epsilon closure is responsible for simulating an unanchored
            // '(?s:.)*?' prefix. It is specifically outside of any
            // capturing groups, and thus, using slots that are always
            // absent is correct.
            //
            // Note though that we can't just use '&mut []' here, since
            // this epsilon closure may traverse through 'Captures' epsilon
            // transitions, and thus must be able to write offsets to the
            // slots given which are later copied to slot values in 'curr'.
            let slots = next.slot_table.all_absent();
            epsilon_closure(vm, stack, slots, curr, input, start_id);
        }
        input.chunk_pos += 1;
        if input.chunk_pos() >= input.chunk().len() {
            input.advance_with_look_behind();
        }
        if let Some(pid) = nexts(vm, stack, curr, next, input, slots) {
            hm = Some(HalfMatch::new(pid, input.at() - 1));
        }
        // Unless the caller asked us to return early, we need to mush on
        // to see if we can extend our match. (But note that 'nexts' will
        // quit right after seeing a match when match_kind==LeftmostFirst,
        // as is consistent with leftmost-first match priority.)
        if input.get_earliest() && hm.is_some() {
            break;
        }
        core::mem::swap(curr, next);
        next.set.clear();
    }
    instrument!(|c| c.eprint(&self.nfa));
    hm
}

/// Process the active states in 'curr' to find the states (written to
/// 'next') we should process for the next byte in the haystack.
///
/// 'stack' is used to perform a depth first traversal of the NFA when
/// computing an epsilon closure.
///
/// When a match is found, the slots for that match state (in 'curr') are
/// copied to 'caps'. Moreover, once a match is seen, processing for 'curr'
/// stops (unless the PikeVM was configured with MatchKind::All semantics).
#[cfg_attr(feature = "perf-inline", inline(always))]
fn nexts<C: Cursor>(
    vm: &PikeVM,
    stack: &mut Vec<FollowEpsilon>,
    curr: &mut ActiveStates,
    next_: &mut ActiveStates,
    input: &mut Input<C>,
    slots: &mut [Option<NonMaxUsize>],
) -> Option<PatternID> {
    instrument!(|c| c.record_state_set(&curr.set));
    let mut pid = None;
    let ActiveStates { ref set, ref mut slot_table } = *curr;
    for sid in set.iter() {
        pid = match next(vm, stack, slot_table, next_, input, sid) {
            None => continue,
            Some(pid) => Some(pid),
        };
        slots.copy_from_slice(slot_table.for_state(sid));
        if vm.get_config().get_match_kind() != MatchKind::All {
            break;
        }
    }
    pid
}

/// Starting from 'sid', if the position 'at' in the 'input' haystack has a
/// transition defined out of 'sid', then add the state transitioned to and
/// its epsilon closure to the 'next' set of states to explore.
///
/// 'stack' is used by the epsilon closure computation to perform a depth
/// first traversal of the NFA.
///
/// 'curr_slot_table' should be the table of slots for the current set of
/// states being explored. If there is a transition out of 'sid', then
/// sid's row in the slot table is used to perform the epsilon closure.
#[cfg_attr(feature = "perf-inline", inline(always))]
fn next<C: Cursor>(
    vm: &PikeVM,
    stack: &mut Vec<FollowEpsilon>,
    curr_slot_table: &mut SlotTable,
    next: &mut ActiveStates,
    input: &mut Input<C>,
    sid: StateID,
) -> Option<PatternID> {
    instrument!(|c| c.record_step(sid));
    let state = vm.get_nfa().state(sid);
    match *state {
        State::Fail
        | State::Look { .. }
        | State::Union { .. }
        | State::BinaryUnion { .. }
        | State::Capture { .. } => None,
        State::ByteRange { ref trans } => {
            let (chunk, pos) = input.look_around();
            if trans.matches(chunk, pos - 1) {
                let slots = curr_slot_table.for_state(sid);
                epsilon_closure(vm, stack, slots, next, input, trans.next);
            }
            None
        }
        State::Sparse(ref sparse) => {
            let (chunk, pos) = input.look_around();
            if let Some(next_sid) = sparse.matches(chunk, pos - 1) {
                let slots = curr_slot_table.for_state(sid);
                epsilon_closure(vm, stack, slots, next, input, next_sid);
            }
            None
        }
        State::Dense(ref dense) => {
            let (chunk, pos) = input.look_around();
            if let Some(next_sid) = dense.matches(chunk, pos - 1) {
                let slots = curr_slot_table.for_state(sid);
                epsilon_closure(vm, stack, slots, next, input, next_sid);
            }
            None
        }
        State::Match { pattern_id } => Some(pattern_id),
    }
}

/// Compute the epsilon closure of 'sid', writing the closure into 'next'
/// while copying slot values from 'curr_slots' into corresponding states
/// in 'next'. 'curr_slots' should be the slot values corresponding to
/// 'sid'.
///
/// The given 'stack' is used to perform a depth first traversal of the
/// NFA by recursively following all epsilon transitions out of 'sid'.
/// Conditional epsilon transitions are followed if and only if they are
/// satisfied for the position 'at' in the 'input' haystack.
///
/// While this routine may write to 'curr_slots', once it returns, any
/// writes are undone and the original values (even if absent) are
/// restored.
#[cfg_attr(feature = "perf-inline", inline(always))]
fn epsilon_closure<C: Cursor>(
    vm: &PikeVM,
    stack: &mut Vec<FollowEpsilon>,
    curr_slots: &mut [Option<NonMaxUsize>],
    next: &mut ActiveStates,
    input: &mut Input<C>,
    sid: StateID,
) {
    instrument!(|c| {
        c.record_closure(sid);
        c.record_stack_push(sid);
    });
    stack.push(FollowEpsilon::Explore(sid));
    while let Some(frame) = stack.pop() {
        match frame {
            FollowEpsilon::RestoreCapture { slot, offset: pos } => {
                curr_slots[slot] = pos;
            }
            FollowEpsilon::Explore(sid) => {
                epsilon_closure_explore(vm, stack, curr_slots, next, input, sid);
            }
        }
    }
}

/// Explore all of the epsilon transitions out of 'sid'. This is mostly
/// split out from 'epsilon_closure' in order to clearly delineate
/// the actual work of computing an epsilon closure from the stack
/// book-keeping.
///
/// This will push any additional explorations needed on to 'stack'.
///
/// 'curr_slots' should refer to the slots for the currently active NFA
/// state. That is, the current state we are stepping through. These
/// slots are mutated in place as new 'Captures' states are traversed
/// during epsilon closure, but the slots are restored to their original
/// values once the full epsilon closure is completed. The ultimate use of
/// 'curr_slots' is to copy them to the corresponding 'next_slots', so that
/// the capturing group spans are forwarded from the currently active state
/// to the next.
///
/// 'next' refers to the next set of active states. Computing an epsilon
/// closure may increase the next set of active states.
///
/// 'input' refers to the caller's input configuration and 'at' refers to
/// the current position in the haystack. These are used to check whether
/// conditional epsilon transitions (like look-around) are satisfied at
/// the current position. If they aren't, then the epsilon closure won't
/// include them.
#[cfg_attr(feature = "perf-inline", inline(always))]
fn epsilon_closure_explore<C: Cursor>(
    vm: &PikeVM,
    stack: &mut Vec<FollowEpsilon>,
    curr_slots: &mut [Option<NonMaxUsize>],
    next: &mut ActiveStates,
    input: &mut Input<C>,
    mut sid: StateID,
) {
    // We can avoid pushing some state IDs on to our stack in precisely
    // the cases where a 'push(x)' would be immediately followed by a 'x
    // = pop()'. This is achieved by this outer-loop. We simply set 'sid'
    // to be the next state ID we want to explore once we're done with
    // our initial exploration. In practice, this avoids a lot of stack
    // thrashing.
    loop {
        instrument!(|c| c.record_set_insert(sid));
        // Record this state as part of our next set of active states. If
        // we've already explored it, then no need to do it again.
        if !next.set.insert(sid) {
            return;
        }
        match *vm.get_nfa().state(sid) {
            State::Fail
            | State::Match { .. }
            | State::ByteRange { .. }
            | State::Sparse { .. }
            | State::Dense { .. } => {
                next.slot_table.for_state(sid).copy_from_slice(curr_slots);
                return;
            }
            State::Look { look, next } => {
                // OK because we don't permit building a searcher with a
                // Unicode word boundary if the requisite Unicode data is
                // unavailable.
                let (chunk, at) = input.look_around();
                if !vm.get_nfa().look_matcher().matches(look, chunk, at) {
                    return;
                }
                sid = next;
            }
            State::Union { ref alternates } => {
                sid = match alternates.get(0) {
                    None => return,
                    Some(&sid) => sid,
                };
                instrument!(|c| {
                    for &alt in &alternates[1..] {
                        c.record_stack_push(alt);
                    }
                });
                stack.extend(alternates[1..].iter().copied().rev().map(FollowEpsilon::Explore));
            }
            State::BinaryUnion { alt1, alt2 } => {
                sid = alt1;
                instrument!(|c| c.record_stack_push(sid));
                stack.push(FollowEpsilon::Explore(alt2));
            }
            State::Capture { next, slot, .. } => {
                // There's no need to do anything with slots that
                // ultimately won't be copied into the caller-provided
                // 'Captures' value. So we just skip dealing with them at
                // all.
                if slot.as_usize() < curr_slots.len() {
                    instrument!(|c| c.record_stack_push(sid));
                    stack.push(FollowEpsilon::RestoreCapture { slot, offset: curr_slots[slot] });
                    // OK because length of a slice must fit into an isize.
                    curr_slots[slot] = Some(NonMaxUsize::new(input.at()).unwrap());
                }
                sid = next;
            }
        }
    }
}
/// A cache represents mutable state that a [`PikeVM`] requires during a
/// search.
///
/// For a given [`PikeVM`], its corresponding cache may be created either via
/// [`PikeVM::create_cache`], or via [`Cache::new`]. They are equivalent in
/// every way, except the former does not require explicitly importing `Cache`.
///
/// A particular `Cache` is coupled with the [`PikeVM`] from which it
/// was created. It may only be used with that `PikeVM`. A cache and its
/// allocations may be re-purposed via [`Cache::reset`], in which case, it can
/// only be used with the new `PikeVM` (and not the old one).
#[derive(Clone, Debug)]
pub struct Cache {
    /// Stack used while computing epsilon closure. This effectively lets us
    /// move what is more naturally expressed through recursion to a stack
    /// on the heap.
    stack: Vec<FollowEpsilon>,
    /// The current active states being explored for the current byte in the
    /// haystack.
    curr: ActiveStates,
    /// The next set of states we're building that will be explored for the
    /// next byte in the haystack.
    next: ActiveStates,
}

impl Cache {
    /// Create a new [`PikeVM`] cache.
    ///
    /// A potentially more convenient routine to create a cache is
    /// [`PikeVM::create_cache`], as it does not require also importing the
    /// `Cache` type.
    ///
    /// If you want to reuse the returned `Cache` with some other `PikeVM`,
    /// then you must call [`Cache::reset`] with the desired `PikeVM`.
    pub fn new(re: &PikeVM) -> Cache {
        Cache { stack: vec![], curr: ActiveStates::new(re), next: ActiveStates::new(re) }
    }

    /// Reset this cache such that it can be used for searching with a
    /// different [`PikeVM`].
    ///
    /// A cache reset permits reusing memory already allocated in this cache
    /// with a different `PikeVM`.
    ///
    /// # Example
    ///
    /// This shows how to re-purpose a cache for use with a different `PikeVM`.
    ///
    /// ```
    /// # if cfg!(miri) { return Ok(()); } // miri takes too long
    /// use regex_automata::{nfa::thompson::pikevm::PikeVM, Match};
    ///
    /// let re1 = PikeVM::new(r"\w")?;
    /// let re2 = PikeVM::new(r"\W")?;
    ///
    /// let mut cache = re1.create_cache();
    /// assert_eq!(
    ///     Some(Match::must(0, 0..2)),
    ///     re1.find_iter(&mut cache, "Δ").next(),
    /// );
    ///
    /// // Using 'cache' with re2 is not allowed. It may result in panics or
    /// // incorrect results. In order to re-purpose the cache, we must reset
    /// // it with the PikeVM we'd like to use it with.
    /// //
    /// // Similarly, after this reset, using the cache with 're1' is also not
    /// // allowed.
    /// cache.reset(&re2);
    /// assert_eq!(
    ///     Some(Match::must(0, 0..3)),
    ///     re2.find_iter(&mut cache, "☃").next(),
    /// );
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn reset(&mut self, re: &PikeVM) {
        self.curr.reset(re);
        self.next.reset(re);
    }

    /// Returns the heap memory usage, in bytes, of this cache.
    ///
    /// This does **not** include the stack size used up by this cache. To
    /// compute that, use `std::mem::size_of::<Cache>()`.
    pub fn memory_usage(&self) -> usize {
        use core::mem::size_of;
        (self.stack.len() * size_of::<FollowEpsilon>())
            + self.curr.memory_usage()
            + self.next.memory_usage()
    }

    /// Clears this cache. This should be called at the start of every search
    /// to ensure we start with a clean slate.
    ///
    /// This also sets the length of the capturing groups used in the current
    /// search. This permits an optimization where by 'SlotTable::for_state'
    /// only returns the number of slots equivalent to the number of slots
    /// given in the 'Captures' value. This may be less than the total number
    /// of possible slots, e.g., when one only wants to track overall match
    /// offsets. This in turn permits less copying of capturing group spans
    /// in the PikeVM.
    fn setup_search(&mut self, captures_slot_len: usize) {
        self.stack.clear();
        self.curr.setup_search(captures_slot_len);
        self.next.setup_search(captures_slot_len);
    }
}

/// Represents a stack frame for use while computing an epsilon closure.
///
/// (An "epsilon closure" refers to the set of reachable NFA states from a
/// single state without consuming any input. That is, the set of all epsilon
/// transitions not only from that single state, but from every other state
/// reachable by an epsilon transition as well. This is why it's called a
/// "closure." Computing an epsilon closure is also done during DFA
/// determinization! Compare and contrast the epsilon closure here in this
/// PikeVM and the one used for determinization in crate::util::determinize.)
///
/// Computing the epsilon closure in a Thompson NFA proceeds via a depth
/// first traversal over all epsilon transitions from a particular state.
/// (A depth first traversal is important because it emulates the same priority
/// of matches that is typically found in backtracking regex engines.) This
/// depth first traversal is naturally expressed using recursion, but to avoid
/// a call stack size proportional to the size of a regex, we put our stack on
/// the heap instead.
///
/// This stack thus consists of call frames. The typical call frame is
/// `Explore`, which instructs epsilon closure to explore the epsilon
/// transitions from that state. (Subsequent epsilon transitions are then
/// pushed on to the stack as more `Explore` frames.) If the state ID being
/// explored has no epsilon transitions, then the capturing group slots are
/// copied from the original state that sparked the epsilon closure (from the
/// 'step' routine) to the state ID being explored. This way, capturing group
/// slots are forwarded from the previous state to the next.
///
/// The other stack frame, `RestoreCaptures`, instructs the epsilon closure to
/// set the position for a particular slot back to some particular offset. This
/// frame is pushed when `Explore` sees a `Capture` transition. `Explore` will
/// set the offset of the slot indicated in `Capture` to the current offset,
/// and then push the old offset on to the stack as a `RestoreCapture` frame.
/// Thus, the new offset is only used until the epsilon closure reverts back to
/// the `RestoreCapture` frame. In effect, this gives the `Capture` epsilon
/// transition its "scope" to only states that come "after" it during depth
/// first traversal.
#[derive(Clone, Debug)]
enum FollowEpsilon {
    /// Explore the epsilon transitions from a state ID.
    Explore(StateID),
    /// Reset the given `slot` to the given `offset` (which might be `None`).
    RestoreCapture { slot: SmallIndex, offset: Option<NonMaxUsize> },
}

/// A set of active states used to "simulate" the execution of an NFA via the
/// PikeVM.
///
/// There are two sets of these used during NFA simulation. One set corresponds
/// to the "current" set of states being traversed for the current position
/// in a haystack. The other set corresponds to the "next" set of states being
/// built, which will become the new "current" set for the next position in the
/// haystack. These two sets correspond to CLIST and NLIST in Thompson's
/// original paper regexes: https://dl.acm.org/doi/pdf/10.1145/363347.363387
///
/// In addition to representing a set of NFA states, this also maintains slot
/// values for each state. These slot values are what turn the NFA simulation
/// into the "Pike VM." Namely, they track capturing group values for each
/// state. During the computation of epsilon closure, we copy slot values from
/// states in the "current" set to the "next" set. Eventually, once a match
/// is found, the slot values for that match state are what we write to the
/// caller provided 'Captures' value.
#[derive(Clone, Debug)]
struct ActiveStates {
    /// The set of active NFA states. This set preserves insertion order, which
    /// is critical for simulating the match semantics of backtracking regex
    /// engines.
    set: SparseSet,
    /// The slots for every NFA state, where each slot stores a (possibly
    /// absent) offset. Every capturing group has two slots. One for a start
    /// offset and one for an end offset.
    slot_table: SlotTable,
}

impl ActiveStates {
    /// Create a new set of active states for the given PikeVM. The active
    /// states returned may only be used with the given PikeVM. (Use 'reset'
    /// to re-purpose the allocation for a different PikeVM.)
    fn new(re: &PikeVM) -> ActiveStates {
        let mut active = ActiveStates { set: SparseSet::new(0), slot_table: SlotTable::new() };
        active.reset(re);
        active
    }

    /// Reset this set of active states such that it can be used with the given
    /// PikeVM (and only that PikeVM).
    fn reset(&mut self, re: &PikeVM) {
        self.set.resize(re.get_nfa().states().len());
        self.slot_table.reset(re);
    }

    /// Return the heap memory usage, in bytes, used by this set of active
    /// states.
    ///
    /// This does not include the stack size of this value.
    fn memory_usage(&self) -> usize {
        self.set.memory_usage() + self.slot_table.memory_usage()
    }

    /// Setup this set of active states for a new search. The given slot
    /// length should be the number of slots in a caller provided 'Captures'
    /// (and may be zero).
    fn setup_search(&mut self, captures_slot_len: usize) {
        self.set.clear();
        self.slot_table.setup_search(captures_slot_len);
    }
}

/// A table of slots, where each row represent a state in an NFA. Thus, the
/// table has room for storing slots for every single state in an NFA.
///
/// This table is represented with a single contiguous allocation. In general,
/// the notion of "capturing group" doesn't really exist at this level of
/// abstraction, hence the name "slot" instead. (Indeed, every capturing group
/// maps to a pair of slots, one for the start offset and one for the end
/// offset.) Slots are indexed by the 'Captures' NFA state.
///
/// N.B. Not every state actually needs a row of slots. Namely, states that
/// only have epsilon transitions currently never have anything written to
/// their rows in this table. Thus, the table is somewhat wasteful in its heap
/// usage. However, it is important to maintain fast random access by state
/// ID, which means one giant table tends to work well. RE2 takes a different
/// approach here and allocates each row as its own reference counted thing.
/// I explored such a strategy at one point here, but couldn't get it to work
/// well using entirely safe code. (To the ambitious reader: I encourage you to
/// re-litigate that experiment.) I very much wanted to stick to safe code, but
/// could be convinced otherwise if there was a solid argument and the safety
/// was encapsulated well.
#[derive(Clone, Debug)]
struct SlotTable {
    /// The actual table of offsets.
    table: Vec<Option<NonMaxUsize>>,
    /// The number of slots per state, i.e., the table's stride or the length
    /// of each row.
    slots_per_state: usize,
    /// The number of slots in the caller-provided 'Captures' value for the
    /// current search. Setting this to 'slots_per_state' is always correct,
    /// but may be wasteful.
    slots_for_captures: usize,
}

impl SlotTable {
    /// Create a new slot table.
    ///
    /// One should call 'reset' with the corresponding PikeVM before use.
    fn new() -> SlotTable {
        SlotTable { table: vec![], slots_for_captures: 0, slots_per_state: 0 }
    }

    /// Reset this slot table such that it can be used with the given PikeVM
    /// (and only that PikeVM).
    fn reset(&mut self, re: &PikeVM) {
        let nfa = re.get_nfa();
        self.slots_per_state = nfa.group_info().slot_len();
        // This is always correct, but may be reduced for a particular search
        // if a 'Captures' has fewer slots, e.g., none at all or only slots
        // for tracking the overall match instead of all slots for every
        // group.
        self.slots_for_captures =
            core::cmp::max(self.slots_per_state, nfa.pattern_len().checked_mul(2).unwrap());
        let len = nfa
            .states()
            .len()
            .checked_mul(self.slots_per_state)
            // Add space to account for scratch space used during a search.
            .and_then(|x| x.checked_add(self.slots_for_captures))
            // It seems like this could actually panic on legitimate inputs on
            // 32-bit targets, and very likely to panic on 16-bit. Should we
            // somehow convert this to an error? What about something similar
            // for the lazy DFA cache? If you're tripping this assert, please
            // file a bug.
            .expect("slot table length doesn't overflow");
        // This happens about as often as a regex is compiled, so it probably
        // should be at debug level, but I found it quite distracting and not
        // particularly useful.
        self.table.resize(len, None);
    }

    /// Return the heap memory usage, in bytes, used by this slot table.
    ///
    /// This does not include the stack size of this value.
    fn memory_usage(&self) -> usize {
        self.table.len() * core::mem::size_of::<Option<NonMaxUsize>>()
    }

    /// Perform any per-search setup for this slot table.
    ///
    /// In particular, this sets the length of the number of slots used in the
    /// 'Captures' given by the caller (if any at all). This number may be
    /// smaller than the total number of slots available, e.g., when the caller
    /// is only interested in tracking the overall match and not the spans of
    /// every matching capturing group. Only tracking the overall match can
    /// save a substantial amount of time copying capturing spans during a
    /// search.
    fn setup_search(&mut self, captures_slot_len: usize) {
        self.slots_for_captures = captures_slot_len;
    }

    /// Return a mutable slice of the slots for the given state.
    ///
    /// Note that the length of the slice returned may be less than the total
    /// number of slots available for this state. In particular, the length
    /// always matches the number of slots indicated via 'setup_search'.
    fn for_state(&mut self, sid: StateID) -> &mut [Option<NonMaxUsize>] {
        let i = sid.as_usize() * self.slots_per_state;
        &mut self.table[i..i + self.slots_for_captures]
    }

    /// Return a slice of slots of appropriate length where every slot offset
    /// is guaranteed to be absent. This is useful in cases where you need to
    /// compute an epsilon closure outside of the user supplied regex, and thus
    /// never want it to have any capturing slots set.
    fn all_absent(&mut self) -> &mut [Option<NonMaxUsize>] {
        let i = self.table.len() - self.slots_for_captures;
        &mut self.table[i..i + self.slots_for_captures]
    }
}

/// An iterator over all non-overlapping matches for a particular search.
///
/// The iterator yields a [`Match`] value until no more matches could be found.
///
/// The lifetime parameters are as follows:
///
/// * `'r` represents the lifetime of the PikeVM.
/// * `'c` represents the lifetime of the PikeVM's cache.
/// * `'h` represents the lifetime of the haystack being searched.
///
/// This iterator can be created with the [`PikeVM::find_iter`] method.
#[derive(Debug)]
pub struct FindMatches<'r, 'c, C: Cursor> {
    re: &'r PikeVM,
    cache: &'c mut Cache,
    caps: Captures,
    it: iter::Searcher<C>,
}

impl<'r, 'c, C: Cursor> Iterator for FindMatches<'r, 'c, C> {
    type Item = Match;

    #[inline]
    fn next(&mut self) -> Option<Match> {
        // Splitting 'self' apart seems necessary to appease borrowck.
        let FindMatches { re, ref mut cache, ref mut caps, ref mut it } = *self;
        // 'advance' converts errors into panics, which is OK here because
        // the PikeVM can never return an error.
        it.advance(|input| {
            search(re, cache, input, caps);
            Ok(caps.get_match())
        })
    }
}
