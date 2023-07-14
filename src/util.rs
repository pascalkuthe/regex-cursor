use crate::Input;
use regex_automata::util::escape::DebugHaystack;

pub(crate) mod empty;
pub mod iter;
pub mod sparse_set;
#[cfg(test)]
mod tests;

/// Returns true if and only if the given offset in the given bytes falls on a
/// valid UTF-8 encoded codepoint boundary.
///
/// If `bytes` is not valid UTF-8, then the behavior of this routine is
/// unspecified.
#[cfg_attr(feature = "perf-inline", inline(always))]
pub(crate) fn is_boundary(byte: Option<u8>) -> bool {
    match byte {
        None => true,
        // Other than ASCII (where the most significant bit is never set),
        // valid starting bytes always have their most significant two bits
        // set, where as continuation bytes never have their second most
        // significant bit set. Therefore, this only returns true when bytes[i]
        // corresponds to a byte that begins a valid UTF-8 encoding of a
        // Unicode scalar value.
        Some(b) => b <= 0b0111_1111 || b >= 0b1100_0000,
    }
}

/// Returns true if and only if the given byte is considered a word character.
/// This only applies to ASCII.
///
/// This was copied from regex-syntax so that we can use it to determine the
/// starting DFA state while searching without depending on regex-syntax. The
/// definition is never going to change, so there's no maintenance/bit-rot
/// hazard here.
#[cfg_attr(feature = "perf-inline", inline(always))]
pub(crate) fn is_word_byte(b: u8) -> bool {
    const fn mkwordset() -> [bool; 256] {
        // FIXME: Use as_usize() once const functions in traits are stable.
        let mut set = [false; 256];
        set[b'_' as usize] = true;

        let mut byte = b'0';
        while byte <= b'9' {
            set[byte as usize] = true;
            byte += 1;
        }
        byte = b'A';
        while byte <= b'Z' {
            set[byte as usize] = true;
            byte += 1;
        }
        byte = b'a';
        while byte <= b'z' {
            set[byte as usize] = true;
            byte += 1;
        }
        set
    }
    const WORD: [bool; 256] = mkwordset();
    WORD[b as usize]
}

/// Decodes the next UTF-8 encoded codepoint from the given byte slice.
///
/// If no valid encoding of a codepoint exists at the beginning of the given
/// byte slice, then the first byte is returned instead.
///
/// This returns `None` if and only if `bytes` is empty.
///
/// This never panics.
///
/// *WARNING*: This is not designed for performance. If you're looking for a
/// fast UTF-8 decoder, this is not it. If you feel like you need one in this
/// crate, then please file an issue and discuss your use case.
#[cfg_attr(feature = "perf-inline", inline(always))]
pub(crate) fn decode(input: &mut Input, at: usize) -> Option<Result<char, u8>> {
    let byte = get_byte(input, at)?;
    let len = match len(byte) {
        None => return Some(Err(byte)),
        Some(1) => return Some(Ok(char::from(byte))),
        Some(len) => len,
    };
    let mut buf = [byte; 4];
    let buf = &mut buf[..len];
    let mut i = 1;
    while i + at < input.haystack().len() && i < buf.len() {
        buf[i] = input.haystack()[i + at];
        i += 1;
    }
    let peek = input.peek();
    while i < buf.len() && i + at - input.haystack().len() < peek.len() {
        buf[i] = *peek.get(i + at - input.haystack().len())?;
        i += 1;
    }

    match core::str::from_utf8(&buf) {
        Ok(s) => Some(Ok(s.chars().next().unwrap())),
        Err(_) => Some(Err(byte)),
    }
}

/// Decodes the last UTF-8 encoded codepoint from the given byte slice.
///
/// If no valid encoding of a codepoint exists at the end of the given byte
/// slice, then the last byte is returned instead.
///
/// This returns `None` if and only if `bytes` is empty.
#[cfg_attr(feature = "perf-inline", inline(always))]
pub(crate) fn decode_last(
    prev_haystack: &[u8],
    input: &mut Input,
    at: usize,
) -> Option<Result<char, u8>> {
    let mut i = 4;
    let mut buf = [0; 4];
    let mut start = at;
    let done = loop {
        if start == 0 {
            break false;
        }
        start -= 1;
        i -= 1;
        buf[i] = input.haystack()[start];
        if i == 0 || is_leading_or_invalid_byte(input.haystack()[start]) {
            break true;
        }
    };
    if !done {
        let mut start = prev_haystack.len().saturating_sub(1);
        loop {
            if start == 0 {
                break;
            }
            start -= 1;
            i -= 1;
            buf[i] = prev_haystack[start];
            if i == 0 || is_leading_or_invalid_byte(prev_haystack[start]) {
                break;
            }
        }
    }
    let byte = *buf.get(i)?;
    match len(byte) {
        None => return Some(Err(byte)),
        Some(len) if i + len != 4 => return Some(Err(byte)),
        Some(1) => return Some(Ok(char::from(byte))),
        Some(_) => (),
    };
    match core::str::from_utf8(&buf[i..]) {
        Ok(s) => Some(Ok(s.chars().next().unwrap())),
        Err(_) => Some(Err(byte)),
    }
}

/// Given a UTF-8 leading byte, this returns the total number of code units
/// in the following encoded codepoint.
///
/// If the given byte is not a valid UTF-8 leading byte, then this returns
/// `None`.
#[cfg_attr(feature = "perf-inline", inline(always))]
fn len(byte: u8) -> Option<usize> {
    if byte <= 0x7F {
        return Some(1);
    } else if byte & 0b1100_0000 == 0b1000_0000 {
        return None;
    } else if byte <= 0b1101_1111 {
        Some(2)
    } else if byte <= 0b1110_1111 {
        Some(3)
    } else if byte <= 0b1111_0111 {
        Some(4)
    } else {
        None
    }
}

/// Returns true if and only if the given byte is either a valid leading UTF-8
/// byte, or is otherwise an invalid byte that can never appear anywhere in a
/// valid UTF-8 sequence.
#[cfg_attr(feature = "perf-inline", inline(always))]
fn is_leading_or_invalid_byte(b: u8) -> bool {
    // In the ASCII case, the most significant bit is never set. The leading
    // byte of a 2/3/4-byte sequence always has the top two most significant
    // bits set. For bytes that can never appear anywhere in valid UTF-8, this
    // also returns true, since every such byte has its two most significant
    // bits set:
    //
    //     \xC0 :: 11000000
    //     \xC1 :: 11000001
    //     \xF5 :: 11110101
    //     \xF6 :: 11110110
    //     \xF7 :: 11110111
    //     \xF8 :: 11111000
    //     \xF9 :: 11111001
    //     \xFA :: 11111010
    //     \xFB :: 11111011
    //     \xFC :: 11111100
    //     \xFD :: 11111101
    //     \xFE :: 11111110
    //     \xFF :: 11111111
    (b & 0b1100_0000) != 0b1000_0000
}

pub(crate) fn prev_byte(prev_haystack: &[u8], input: &Input, at: usize) -> Option<u8> {
    match at.checked_sub(1) {
        Some(at_m_1) => Some(input.haystack()[at_m_1]),
        None => prev_haystack.get(0).copied(),
    }
}

pub(crate) fn get_byte(input: &mut Input, at: usize) -> Option<u8> {
    input.haystack().get(at).or_else(|| input.peek().get(at - input.haystack().len())).copied()
}
