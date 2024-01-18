pub use regex_automata::util::prefilter::Prefilter;
pub use regex_automata::MatchKind;
use regex_automata::Span;

use crate::cursor::Cursor;
use crate::Input;

#[cfg(test)]
mod tests;

pub fn find<C: Cursor>(prefilter: &Prefilter, input: &mut Input<C>) -> Option<Span> {
    if prefilter.max_needle_len() == 1 {
        find_1(prefilter, input)
    } else {
        find_n(prefilter, input)
    }
}

pub fn prefix<C: Cursor>(prefilter: &Prefilter, input: &mut Input<C>) -> Option<Span> {
    let mut offset = input.chunk_offset();
    let chunk_pos = input.chunk_pos();
    let chunk_end = input.get_chunk_end();
    let mut res = if prefilter.max_needle_len() <= chunk_end - chunk_pos {
        prefilter
            .prefix(input.chunk(), Span { start: input.chunk_pos(), end: input.get_chunk_end() })?
    } else {
        offset += chunk_pos;
        let mut buf = Vec::with_capacity(prefilter.max_needle_len());
        buf.extend_from_slice(&input.chunk()[chunk_pos..chunk_end]);
        while input.advance() {
            if input.chunk_offset() + input.chunk().len() < input.end() {
                buf.extend_from_slice(input.chunk());
            } else {
                let chunk_end = input.end() - input.chunk_offset();
                buf.extend_from_slice(&input.chunk()[..chunk_end]);
                break;
            }
        }
        prefilter.prefix(input.chunk(), Span { start: 0, end: buf.len() })?
    };
    res.start += offset;
    res.end += offset;
    Some(res)
}

fn find_1<C: Cursor>(prefilter: &Prefilter, input: &mut Input<C>) -> Option<Span> {
    debug_assert_eq!(prefilter.max_needle_len(), 1);
    let first_haystack = &input.chunk();
    if let Some(mut res) = prefilter
        .find(first_haystack, Span { start: input.chunk_pos(), end: input.get_chunk_end() })
    {
        res.start += input.chunk_offset();
        res.end += input.chunk_offset();
        return Some(res);
    }
    while input.chunk_offset() + input.chunk().len() < input.end() && input.advance() {
        let haystack = &input.chunk();
        let Some(mut res) = prefilter.find(haystack, Span { start: 0, end: input.get_chunk_end() })
        else {
            continue;
        };

        res.start += input.chunk_offset();
        res.end += input.chunk_offset();
        return Some(res);
    }
    None
}

fn find_n<C: Cursor>(prefilter: &Prefilter, input: &mut Input<C>) -> Option<Span> {
    let carry_over = prefilter.max_needle_len() - 1;
    let sliding_window = 2 * carry_over;
    let mut buf = Vec::with_capacity(3 * carry_over);
    if let Some(mut res) =
        prefilter.find(input.chunk(), Span { start: input.chunk_pos(), end: input.get_chunk_end() })
    {
        res.start += input.chunk_offset();
        res.end += input.chunk_offset();
        return Some(res);
    }
    #[cfg(debug_assertions)]
    let mut found_large_chunk = false;

    while input.chunk_offset() + input.chunk().len() < input.end() {
        #[cfg(debug_assertions)]
        assert!(
            buf.is_empty()
                || (buf.len() < sliding_window && (buf.len() >= carry_over || !found_large_chunk)),
            "{} {} {}",
            buf.len(),
            carry_over,
            found_large_chunk
        );
        let carry_over_start = input.chunk().len() - carry_over.min(input.chunk().len());
        buf.extend_from_slice(&input.chunk()[carry_over_start..]);
        if buf.len() >= sliding_window {
            if let Some(mut res) = prefilter.find(&buf, Span { start: 0, end: buf.len() }) {
                let buf_offset = input.chunk_offset() - buf.len();
                res.start += buf_offset;
                res.end += buf_offset;
                return Some(res);
            }
            // rotate the end of the buffer
            let shift_len = buf.len() - carry_over;
            let (head, tail) = buf.split_at_mut(shift_len);
            head[..carry_over].copy_from_slice(tail);
            buf.truncate(carry_over);
        }
        if !input.advance() {
            break;
        }
        if input.get_chunk_end() + buf.len() < sliding_window {
            continue;
        }

        #[cfg(debug_assertions)]
        {
            found_large_chunk = true;
        }

        // assumption: its faster to copy and search on the contigous slice here
        // TODO: verify with benchmarks
        if input.get_chunk_end() + buf.len() < buf.capacity() {
            let buf_offset = input.chunk_offset() - buf.len();
            buf.extend_from_slice(input.chunk());
            if let Some(mut res) = prefilter.find(&buf, Span { start: 0, end: buf.len() }) {
                res.start += buf_offset;
                res.end += buf_offset;
                return Some(res);
            }
        } else {
            let buf_offset = input.chunk_offset() - buf.len();
            buf.extend_from_slice(&input.chunk()[..carry_over]);
            if let Some(mut res) = prefilter.find(&buf, Span { start: 0, end: buf.len() }) {
                res.start += buf_offset;
                res.end += buf_offset;
                return Some(res);
            }
            if let Some(mut res) =
                prefilter.find(input.chunk(), Span { start: 0, end: input.get_chunk_end() })
            {
                res.start += input.chunk_offset();
                res.end += input.chunk_offset();
                return Some(res);
            }
        }
        buf.clear();
    }
    // this is a really weird edgecase where the total string is smaller than the
    // longest neeldle len but larger than the shortest needel
    if !buf.is_empty() {
        if let Some(mut res) = prefilter.find(&buf, Span { start: 0, end: buf.len() }) {
            let buf_offset = input.chunk_offset() - buf.len();
            res.start += buf_offset;
            res.end += buf_offset;
            return Some(res);
        }
    }
    None
}
