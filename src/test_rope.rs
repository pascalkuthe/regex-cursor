use std::cell::Cell;
use std::collections::hash_map::DefaultHasher;
use std::hash::Hasher;
use std::sync::atomic::{AtomicUsize, Ordering};

use regex_automata::util::escape::DebugHaystack;

use crate::Cursor;

struct XorShift64Star {
    state: Cell<u64>,
}

impl XorShift64Star {
    fn new() -> Self {
        // Any non-zero seed will do -- this uses the hash of a global counter.
        let mut seed = 0;
        while seed == 0 {
            let mut hasher = DefaultHasher::new();
            static COUNTER: AtomicUsize = AtomicUsize::new(0);
            hasher.write_usize(COUNTER.fetch_add(1, Ordering::Relaxed));
            seed = hasher.finish();
        }

        XorShift64Star { state: Cell::new(seed) }
    }

    fn next(&self) -> u64 {
        let mut x = self.state.get();
        debug_assert_ne!(x, 0);
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.state.set(x);
        x.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    /// Return a value from `0..n`.
    fn next_usize(&self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

pub(crate) struct SegmentedSlice<'a> {
    haystack: &'a [u8],
    pos: usize,
    size: usize,
    ran: XorShift64Star,
}

impl<'a> SegmentedSlice<'a> {
    pub fn new(haystack: &'a [u8]) -> Self {
        let mut res = SegmentedSlice { haystack, pos: 0, size: 0, ran: XorShift64Star::new() };
        res.advance();
        res
    }
}

impl Cursor for SegmentedSlice<'_> {
    fn chunk(&self) -> &[u8] {
        debug_assert_eq!(self.haystack.is_empty(), self.size == 0);
        &self.haystack[self.pos..self.pos + self.size]
    }

    fn utf8_aware(&self) -> bool {
        true
    }

    fn advance(&mut self) -> bool {
        if self.pos + self.size == self.haystack.len() {
            return false;
        }
        let new_start = self.pos + self.size;
        let mut tries = u16::MAX;
        loop {
            let next_size = self.ran.next_usize(250) + 1;
            let new_end = (new_start + next_size).min(self.haystack.len());
            if crate::util::utf8::is_boundary(self.haystack, new_end) {
                self.pos = new_start;
                self.size = new_end - new_start;
                break;
            }
            if tries == 0 {
                panic!("faild to advance at {} {:?}", self.pos, DebugHaystack(self.haystack))
            }
            tries -= 1;
        }
        true
    }

    fn backtrack(&mut self) -> bool {
        if self.pos == 0 {
            return false;
        }
        let mut tries = u16::MAX;
        let new_end = self.pos;
        loop {
            let next_size = self.ran.next_usize(250) + 1;
            let new_start = new_end.saturating_sub(next_size);
            if crate::util::utf8::is_boundary(self.haystack, new_start) {
                self.pos = new_start;
                self.size = new_end - new_start;
                break;
            }
            if tries == 0 {
                panic!("faild to backtrack at {} {:?}", self.pos, DebugHaystack(self.haystack))
            }
            tries -= 1;
        }
        true
    }
}
