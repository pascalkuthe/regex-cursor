/*!
Utilities for dealing with UTF-8.

This module provides some UTF-8 related helper routines, including an
incremental decoder.
*/

/// Returns true if and only if the given offset in the given bytes falls on a
/// valid UTF-8 encoded codepoint boundary.
///
/// If `bytes` is not valid UTF-8, then the behavior of this routine is
/// unspecified.
#[cfg_attr(feature = "perf-inline", inline(always))]
pub(crate) fn is_boundary(bytes: &[u8], i: usize) -> bool {
    match bytes.get(i) {
        // The position at the end of the bytes always represents an empty
        // string, which is a valid boundary. But anything after that doesn't
        // make much sense to call valid a boundary.
        None => i == bytes.len(),
        // Other than ASCII (where the most significant bit is never set),
        // valid starting bytes always have their most significant two bits
        // set, where as continuation bytes never have their second most
        // significant bit set. Therefore, this only returns true when bytes[i]
        // corresponds to a byte that begins a valid UTF-8 encoding of a
        // Unicode scalar value.
        Some(&b) => b <= 0b0111_1111 || b >= 0b1100_0000,
    }
}
