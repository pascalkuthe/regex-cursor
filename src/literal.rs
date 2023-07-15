use regex_automata::util::prefilter::Prefilter as Impl;
pub use regex_automata::MatchKind;
use regex_automata::Span;

use crate::Input;

#[cfg(test)]
mod tests;

/// HACKS: we rely on implementation details of ropey to accelerate
/// (the extremly common) case where the needle is as small as the
/// minimum chunk width. Cessen will not like this but its just too
/// tempting.
///
/// I think this is ok for the follwoing reasons:
/// * there are essentially only two scenarios where this limit does not hold
///    * the root node if its a leave: in that case there is only a single
///      chunk, we only rely on this for multi chunks
///    * If the text begins or ends with a CRLF pair (or multibyte char) that
///      just pushed it over the edge in specific circumstances, then the leaf node
///      that contains it must exceed `MAX_BYTES` to avoid splitting it.  This should be
///      extremely rare and to account for it we substract 3 bytes form the actual limit
///      to be save.
/// * literal optimization speedup regex by (up to) an order of magnitude, but are basically not worth it if literal are spread across more than two chunks
/// * the ropey version is pinned
/// * I am fairly involved in ropey and would notice if this changed
const ROPEY_MIN_CHUNK_LEN: usize = 29;

#[derive(Clone, Debug)]
pub struct Prefilter {
    inner: Impl,
    max_needle_len: usize,
}

impl Prefilter {
    pub fn new<B: AsRef<[u8]>>(kind: MatchKind, needles: &[B]) -> Option<Prefilter> {
        Impl::new(kind, needles).and_then(|inner| {
            let max_needle_len = needles
                .iter()
                .map(|needle| needle.as_ref().len())
                .max()
                .expect("atleast one needle required for construction prefilter");
            // super long needles are super rare/mostly just not worth it. Just
            // let the dfa handle that we are just prefiltering here after al
            if max_needle_len > ROPEY_MIN_CHUNK_LEN {
                return None;
            }
            Some(Prefilter { inner, max_needle_len })
        })
    }
    pub fn wrap<B: AsRef<[u8]>>(imp: Option<Impl>, needles: &[B]) -> Option<Prefilter> {
        imp.and_then(|inner| {
            let max_needle_len = needles
                .iter()
                .map(|needle| needle.as_ref().len())
                .max()
                .expect("atleast one needle required for construction prefilter");
            // super long needles are super rare/mostly just not worth it. Just
            // let the dfa handle that we are just prefiltering here after al
            if max_needle_len > ROPEY_MIN_CHUNK_LEN {
                return None;
            }
            Some(Prefilter { inner, max_needle_len })
        })
    }

    pub fn find(&self, input: &mut Input, span: Span) -> Option<Span> {
        let old_span = input.get_span();
        input.set_span(span);
        let res = if self.max_needle_len == 1 { self.find_1(input) } else { self.find_n(input) };
        input.set_span(old_span);
        res
    }

    fn find_1(&self, input: &mut Input) -> Option<Span> {
        debug_assert_eq!(self.max_needle_len, 1);
        let start = input.move_to(input.start())?;
        let first_haystack = input.haystack_fwd_truncated();
        if let Some(mut res) =
            self.inner.find(first_haystack, Span { start, end: first_haystack.len() })
        {
            res.start += input.haystack_off();
            res.end += input.haystack_off();
            return Some(res);
        }
        loop {
            input.advance_fwd()?;
            let haystack = input.haystack_fwd_truncated();
            let Some(mut res) =
                self.inner.find(haystack, Span { start: 0, end: first_haystack.len() })
            else {
                continue;
            };

            res.start += input.haystack_off();
            res.end += input.haystack_off();
            return Some(res);
        }
    }

    fn find_n(&self, input: &mut Input) -> Option<Span> {
        // ropey chunks are never smaller than 30
        let carry_over = self.max_needle_len - 1;
        debug_assert!(carry_over <= ROPEY_MIN_CHUNK_LEN);
        let mut buf = Vec::with_capacity(self.max_needle_len * 2 - 2);
        let start = input.move_to(input.start())?;
        let first_haystack = input.haystack_fwd_truncated();
        if let Some(mut res) =
            self.inner.find(first_haystack, Span { start, end: first_haystack.len() })
        {
            res.start += input.haystack_off();
            res.end += input.haystack_off();
            return Some(res);
        }
        let prev_haystack_off = input.haystack_off();
        input.advance_fwd()?;
        let haystack = input.haystack_fwd_truncated();
        let carry_over_start = first_haystack.len().saturating_sub(carry_over);
        buf.extend_from_slice(&first_haystack[carry_over_start..]);
        buf.extend_from_slice(&haystack[..carry_over.min(haystack.len())]);
        if let Some(mut res) = self.inner.find(&buf, Span { start: 0, end: buf.len() }) {
            res.start += prev_haystack_off + carry_over_start;
            res.end += prev_haystack_off + carry_over_start;
            return Some(res);
        }
        loop {
            let haystack = input.haystack_fwd_truncated();
            if let Some(mut res) = self.inner.find(haystack, Span { start: 0, end: haystack.len() })
            {
                res.start += input.haystack_off();
                res.end += input.haystack_off();
                return Some(res);
            }

            let prev_haystack = haystack;
            let prev_haystack_off = input.haystack_off();
            input.advance_fwd()?;
            let carry_over_start = prev_haystack.len().saturating_sub(carry_over);
            let haystack = input.haystack_fwd_truncated();
            buf.extend_from_slice(&prev_haystack[prev_haystack.len().saturating_sub(carry_over)..]);
            buf.extend_from_slice(&haystack[..carry_over.min(haystack.len())]);
            if let Some(mut res) = self.inner.find(&buf, Span { start: 0, end: buf.len() }) {
                res.start += prev_haystack_off + carry_over_start;
                res.end += prev_haystack_off + carry_over_start;
                return Some(res);
            }
            buf.clear();
        }
    }

    // fn prefix(&self, haystack: &[u8], span: Span) -> Option<Span> {
    //     self.inner.prefix(haystack, span)
    // }

    fn memory_usage(&self) -> usize {
        self.inner.memory_usage()
    }

    // fn is_fast(&self) -> bool {
    //     self.inner.is_fast()
    // }
}

// fn search()
