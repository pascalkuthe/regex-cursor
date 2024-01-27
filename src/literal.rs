pub use regex_automata::util::prefilter::Prefilter;
pub use regex_automata::MatchKind;
use regex_automata::Span;

use crate::cursor::Cursor;
use crate::Input;

use FindChunkResult::*;

#[cfg(test)]
mod tests;

pub fn find<C: Cursor>(prefilter: &Prefilter, input: &mut Input<C>) -> Option<Span> {
    // TODO optimize this:
    // * potentially use an array vec
    // * specical case max_needle_len==2 (no accumulating necessary)
    // * specical case max_needle_len==min_needle_len (no ambiguety)
    if prefilter.max_needle_len() == 1 {
        find_1(prefilter, input)
    } else {
        find_n::<C, true>(prefilter, input)
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
        let mut buf =
            Vec::with_capacity(prefilter.max_needle_len().min(input.end() - input.start()));
        buf.extend_from_slice(&input.chunk()[chunk_pos..chunk_end]);
        while input.advance() && !buf.spare_capacity_mut().is_empty() {
            let mut chunk_len = input.chunk().len().min(buf.spare_capacity_mut().len());
            if input.chunk_offset() + chunk_len <= input.end() {
                buf.extend_from_slice(&input.chunk()[..chunk_len]);
            } else {
                chunk_len = input.end() - input.chunk_offset();
                buf.extend_from_slice(&input.chunk()[..chunk_len]);
                break;
            }
        }
        prefilter.prefix(&buf, Span { start: 0, end: buf.len() })?
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

fn find_n<C: Cursor, const AMBIGUITY: bool>(
    prefilter: &Prefilter,
    input: &mut Input<C>,
) -> Option<Span> {
    // helper macro to make the code more readable
    macro_rules! find_chunk {
        ($chunk:expr, $buf_offset:expr, |$start: ident, $off: ident| $disambiguate: expr) => {
            match find_n_chunk::<AMBIGUITY>(prefilter, $chunk, $buf_offset) {
                FindChunkResult::Match(span) => return Some(span),
                FindChunkResult::AbigousMatch { $start, $off } if AMBIGUITY => {
                    return Some($disambiguate);
                }
                _ => {}
            }
        };
    }

    // simple case: only search in a single chunk specical casing this is nice
    // for performance and makes the rest of the logic simpler
    let first_chunk_end = input.get_chunk_end();
    let mut first_chunk = input.chunk();
    if first_chunk.len() != first_chunk_end {
        if let Some(mut res) =
            prefilter.find(first_chunk, Span { start: input.chunk_pos(), end: first_chunk_end })
        {
            res.start += input.chunk_offset();
            res.end += input.chunk_offset();
            return Some(res);
        }
        return None;
    }
    first_chunk = &first_chunk[input.chunk_pos()..];

    let max_needle_len = prefilter.max_needle_len();
    let carry_over = max_needle_len - 1;
    let sliding_window = 2 * carry_over;

    // again special case the first chunk since that is the hot path
    // and also keeps the logic below simpler
    let mut buf_offset = input.chunk_offset() + input.chunk_pos();
    if first_chunk.len() >= sliding_window {
        find_chunk!(first_chunk, input.chunk_offset() + input.chunk_pos(), |start, off| {
            let mut buf = Vec::with_capacity(max_needle_len);
            buf.extend_from_slice(&first_chunk[start..]);
            disambiguate_match(prefilter, input, buf, off)
        });
        let carrry_over_start = first_chunk.len() - carry_over;
        first_chunk = &first_chunk[carrry_over_start..];
        buf_offset += carrry_over_start;
    }
    let mut buf = Vec::with_capacity(2 * sliding_window);
    buf.extend_from_slice(first_chunk);

    while input.chunk_offset() + input.chunk().len() < input.end() && input.advance() {
        debug_assert!(buf.len() < sliding_window, "{} {sliding_window}", buf.len());
        let mut chunk = &input.chunk()[..input.get_chunk_end()];
        let mut chunk_offset = input.chunk_offset();
        // this condition only triggers until we have filled the buffer for the first time
        if buf.len() < carry_over {
            if buf.len() + chunk.len() <= carry_over {
                buf.extend_from_slice(chunk);
                continue;
            }
            let copied = carry_over - buf.len();
            buf.extend_from_slice(&chunk[..copied]);
            chunk = &chunk[copied..];
            chunk_offset += copied;
        }
        debug_assert!(buf.len() >= carry_over, "{} {carry_over}", buf.len());

        // if the chunk is too small just continue accumelating the condition
        // below implies chunk.len() <= sliding_window since buf.len() <=
        // sliding_window
        if buf.len() + chunk.len() <= buf.capacity() {
            buf.extend_from_slice(chunk);
            if buf.len() >= sliding_window {
                find_chunk!(&buf, buf_offset, |start, off| {
                    buf.drain(..start);
                    disambiguate_match(prefilter, input, buf, off)
                });
                let carry_over_start = buf.len() - carry_over;
                buf.drain(..carry_over_start);
                buf_offset += carry_over_start;
            }
            continue;
        }

        buf.extend_from_slice(&chunk[..carry_over]);
        find_chunk!(&buf, buf_offset, |start, off| {
            buf.drain(..start);
            buf.extend_from_slice(&chunk[..max_needle_len - buf.len()]);
            let mut res = prefilter.prefix(&buf, Span { start: 0, end: buf.len() }).unwrap();
            res.start += off;
            res.end += off;
            res
        });
        buf.clear();

        find_chunk!(chunk, chunk_offset, |start, off| {
            buf.extend_from_slice(&chunk[start..]);
            disambiguate_match(prefilter, input, buf, off)
        });
        let carrry_over_start = chunk.len() - carry_over;
        buf_offset = chunk_offset + carrry_over_start;
        buf.extend_from_slice(&chunk[carrry_over_start..]);
    }

    if !buf.is_empty() {
        if let Some(mut res) = prefilter.find(&buf, Span { start: 0, end: buf.len() }) {
            res.start += buf_offset;
            res.end += buf_offset;
            return Some(res);
        }
    }
    None
}

#[must_use]
enum FindChunkResult {
    // the prefilter found no matches in this chunk
    NoMatch,
    // the prefilter found a match at the (offset correctd)
    // span in this chunk
    Match(Span),
    // the prefilter found a match that could be ambigous
    // depending on what data follows the buffer
    AbigousMatch { start: usize, off: usize },
}

fn disambiguate_match<C: Cursor>(
    prefilter: &Prefilter,
    input: &mut Input<C>,
    mut buf: Vec<u8>,
    off: usize,
) -> Span {
    let max_needle_len = prefilter.max_needle_len();
    debug_assert!(buf.len() < max_needle_len);
    while input.advance() {
        let chunk_end = input.get_chunk_end().min(max_needle_len - buf.len());
        let chunk = input.chunk();
        if chunk_end != chunk.len() {
            buf.extend_from_slice(&chunk[..chunk_end]);
            break;
        }
        buf.extend_from_slice(chunk);
    }
    debug_assert!(buf.len() <= max_needle_len);
    let mut res = prefilter.prefix(&buf, Span { start: 0, end: buf.len() }).unwrap();
    res.start += off;
    res.end += off;
    res
}

fn find_n_chunk<const AMBIGOUS: bool>(
    prefilter: &Prefilter,
    buf: &[u8],
    off: usize,
) -> FindChunkResult {
    debug_assert!(buf.len() >= 2 * prefilter.max_needle_len() - 2);
    if let Some(mut res) = prefilter.find(buf, Span { start: 0, end: buf.len() }) {
        // This condition is neeed in case we find a match at the end of the
        // chunk. In that case there may be an even longer match once we
        // continue scanning. For example:
        //
        // pattern: "abc|a"
        // haystack: "xxabc" chunked into ["xxab", "c"]
        // matck_kind: leftmost-first
        //
        // In the first chunk we would find a match for "a" but we
        // should be matching "abc" instead (since that is the first
        // alternation).
        if AMBIGOUS && res.start + prefilter.max_needle_len() > buf.len() {
            AbigousMatch { start: res.start, off: res.start + off }
        } else {
            res.start += off;
            res.end += off;
            Match(res)
        }
    } else {
        NoMatch
    }
}
