use regex_automata::util::escape::DebugByte;
use regex_automata::util::look::{Look, LookSet, UnicodeWordBoundaryError};

use crate::util::{decode, decode_last, get_byte, is_word_byte, prev_byte};
use crate::Input;

/// A matcher for look-around assertions.
///
/// This matcher permits configuring aspects of how look-around assertions are
/// matched.
///
/// # Example
///
/// A `LookMatcher` can change the line terminator used for matching multi-line
/// anchors such as `(?m:^)` and `(?m:$)`.
///
/// ```
/// use regex_automata::{
///     nfa::thompson::{self, pikevm::PikeVM},
///     util::look::LookMatcher,
///     Match, Input,
/// };
///
/// let mut lookm = LookMatcher::new();
/// lookm.set_line_terminator(b'\x00');
///
/// let re = PikeVM::builder()
///     .thompson(thompson::Config::new().look_matcher(lookm))
///     .build(r"(?m)^[a-z]+$")?;
/// let mut cache = re.create_cache();
///
/// // Multi-line assertions now use NUL as a terminator.
/// assert_eq!(
///     Some(Match::must(0, 1..4)),
///     re.find(&mut cache, b"\x00abc\x00"),
/// );
/// // ... and \n is no longer recognized as a terminator.
/// assert_eq!(
///     None,
///     re.find(&mut cache, b"\nabc\n"),
/// );
///
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Debug)]
pub struct LookMatcher {
    lineterm: DebugByte,
}

impl LookMatcher {
    /// Creates a new default matcher for look-around assertions.
    pub fn new() -> LookMatcher {
        LookMatcher { lineterm: DebugByte(b'\n') }
    }

    /// Sets the line terminator for use with `(?m:^)` and `(?m:$)`.
    ///
    /// Namely, instead of `^` matching after `\n` and `$` matching immediately
    /// before a `\n`, this will cause it to match after and before the byte
    /// given.
    ///
    /// It can occasionally be useful to use this to configure the line
    /// terminator to the NUL byte when searching binary data.
    ///
    /// Note that this does not apply to CRLF-aware line anchors such as
    /// `(?Rm:^)` and `(?Rm:$)`. CRLF-aware line anchors are hard-coded to
    /// use `\r` and `\n`.
    pub fn set_line_terminator(&mut self, byte: u8) -> &mut LookMatcher {
        self.lineterm.0 = byte;
        self
    }

    /// Returns the line terminator that was configured for this matcher.
    ///
    /// If no line terminator was configured, then this returns `\n`.
    ///
    /// Note that the line terminator should only be used for matching `(?m:^)`
    /// and `(?m:$)` assertions. It specifically should _not_ be used for
    /// matching the CRLF aware assertions `(?Rm:^)` and `(?Rm:$)`.
    pub fn get_line_terminator(&self) -> u8 {
        self.lineterm.0
    }

    // /// Returns true when the position `at` in `haystack` satisfies the given
    // /// look-around assertion.
    // ///
    // /// # Panics
    // ///
    // /// This panics when testing any Unicode word boundary assertion in this
    // /// set and when the Unicode word data is not available. Specifically, this
    // /// only occurs when the `unicode-word-boundary` feature is not enabled.
    // ///
    // /// Since it's generally expected that this routine is called inside of
    // /// a matching engine, callers should check the error condition when
    // /// building the matching engine. If there is a Unicode word boundary
    // /// in the matcher and the data isn't available, then the matcher should
    // /// fail to build.
    // ///
    // /// Callers can check the error condition with [`LookSet::available`].
    // ///
    // /// This also may panic when `at > haystack.len()`. Note that `at ==
    // /// haystack.len()` is legal and guaranteed not to panic.
    // #[inline]
    // pub fn matches(&self, look: Look, haystack: &[u8], at: usize) -> bool {
    //     self.matches_inline(look, haystack, at)
    // }

    /// Like `matches`, but forcefully inlined.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn matches_inline(
        &self,
        look: Look,
        prev_haystack: &[u8],
        input: &mut Input,
        at: usize,
    ) -> bool {
        match look {
            Look::Start => self.is_start(input, at),
            Look::End => self.is_end(input, at),
            Look::StartLF => self.is_start_lf(prev_haystack, input, at),
            Look::EndLF => self.is_end_lf(input, at),
            Look::StartCRLF => self.is_start_crlf(prev_haystack, input, at),
            Look::EndCRLF => self.is_end_crlf(prev_haystack, input, at),
            Look::WordAscii => self.is_word_ascii(prev_haystack, input, at),
            Look::WordAsciiNegate => self.is_word_ascii_negate(prev_haystack, input, at),
            Look::WordUnicode => self.is_word_unicode(prev_haystack, input, at).unwrap(),
            Look::WordUnicodeNegate => {
                self.is_word_unicode_negate(prev_haystack, input, at).unwrap()
            }
        }
    }

    /// Returns true when _all_ of the assertions in the given set match at the
    /// given position in the haystack.
    ///
    /// # Panics
    ///
    /// This panics when testing any Unicode word boundary assertion in this
    /// set and when the Unicode word data is not available. Specifically, this
    /// only occurs when the `unicode-word-boundary` feature is not enabled.
    ///
    /// Since it's generally expected that this routine is called inside of
    /// a matching engine, callers should check the error condition when
    /// building the matching engine. If there is a Unicode word boundary
    /// in the matcher and the data isn't available, then the matcher should
    /// fail to build.
    ///
    /// Callers can check the error condition with [`LookSet::available`].
    ///
    /// This also may panic when `at > haystack.len()`. Note that `at ==
    /// haystack.len()` is legal and guaranteed not to panic.
    #[inline]
    pub fn matches_set(
        &self,
        set: LookSet,
        prev_haystack: &[u8],
        input: &mut Input,
        at: usize,
    ) -> bool {
        self.matches_set_inline(set, prev_haystack, input, at)
    }

    /// Like `LookSet::matches`, but forcefully inlined for perf.
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn matches_set_inline(
        &self,
        set: LookSet,
        prev_haystack: &[u8],
        input: &mut Input,
        at: usize,
    ) -> bool {
        // This used to luse LookSet::iter with Look::matches on each element,
        // but that proved to be quite diastrous for perf. The manual "if
        // the set has this assertion, check it" turns out to be quite a bit
        // faster.
        if set.contains(Look::Start) {
            if !self.is_start(input, at) {
                return false;
            }
        }
        if set.contains(Look::End) {
            if !self.is_end(input, at) {
                return false;
            }
        }
        if set.contains(Look::StartLF) {
            if !self.is_start_lf(prev_haystack, input, at) {
                return false;
            }
        }
        if set.contains(Look::EndLF) {
            if !self.is_end_lf(input, at) {
                return false;
            }
        }
        if set.contains(Look::StartCRLF) {
            if !self.is_start_crlf(prev_haystack, input, at) {
                return false;
            }
        }
        if set.contains(Look::EndCRLF) {
            if !self.is_end_crlf(prev_haystack, input, at) {
                return false;
            }
        }
        if set.contains(Look::WordAscii) {
            if !self.is_word_ascii(prev_haystack, input, at) {
                return false;
            }
        }
        if set.contains(Look::WordAsciiNegate) {
            if !self.is_word_ascii_negate(prev_haystack, input, at) {
                return false;
            }
        }
        if set.contains(Look::WordUnicode) {
            if !self.is_word_unicode(prev_haystack, input, at).unwrap() {
                return false;
            }
        }
        if set.contains(Look::WordUnicodeNegate) {
            if !self.is_word_unicode_negate(prev_haystack, input, at).unwrap() {
                return false;
            }
        }
        true
    }

    /// Split up the given byte classes into equivalence classes in a way that
    /// is consistent with this look-around assertion.
    #[cfg(feature = "alloc")]
    pub(crate) fn add_to_byteset(&self, look: Look, set: &mut crate::util::alphabet::ByteClassSet) {
        match look {
            Look::Start | Look::End => {}
            Look::StartLF | Look::EndLF => {
                set.set_range(self.lineterm.0, self.lineterm.0);
            }
            Look::StartCRLF | Look::EndCRLF => {
                set.set_range(b'\r', b'\r');
                set.set_range(b'\n', b'\n');
            }
            Look::WordAscii
            | Look::WordAsciiNegate
            | Look::WordUnicode
            | Look::WordUnicodeNegate => {
                // We need to mark all ranges of bytes whose pairs result in
                // evaluating \b differently. This isn't technically correct
                // for Unicode word boundaries, but DFAs can't handle those
                // anyway, and thus, the byte classes don't need to either
                // since they are themselves only used in DFAs.
                //
                // FIXME: It seems like the calls to 'set_range' here are
                // completely invariant, which means we could just hard-code
                // them here without needing to write a loop. And we only need
                // to do this dance at most once per regex.
                //
                // FIXME: Is this correct for \B?
                let iswb = utf8::is_word_byte;
                // This unwrap is OK because we guard every use of 'asu8' with
                // a check that the input is <= 255.
                let asu8 = |b: u16| u8::try_from(b).unwrap();
                let mut b1: u16 = 0;
                let mut b2: u16;
                while b1 <= 255 {
                    b2 = b1 + 1;
                    while b2 <= 255 && iswb(asu8(b1)) == iswb(asu8(b2)) {
                        b2 += 1;
                    }
                    // The guards above guarantee that b2 can never get any
                    // bigger.
                    assert!(b2 <= 256);
                    // Subtracting 1 from b2 is always OK because it is always
                    // at least 1 greater than b1, and the assert above
                    // guarantees that the asu8 conversion will succeed.
                    set.set_range(asu8(b1), asu8(b2.checked_sub(1).unwrap()));
                    b1 = b2;
                }
            }
        }
    }

    /// Returns true when [`Look::Start`] is satisfied `at` the given position
    /// in `haystack`.
    ///
    /// # Panics
    ///
    /// This may panic when `at > haystack.len()`. Note that `at ==
    /// haystack.len()` is legal and guaranteed not to panic.
    #[inline]
    pub fn is_start(&self, input: &Input, at: usize) -> bool {
        at == 0 && input.haystack_off() == 0
    }

    /// Returns true when [`Look::End`] is satisfied `at` the given position in
    /// `haystack`.
    ///
    /// # Panics
    ///
    /// This may panic when `at > haystack.len()`. Note that `at ==
    /// haystack.len()` is legal and guaranteed not to panic.
    #[inline]
    pub fn is_end(&self, input: &Input, at: usize) -> bool {
        at + input.haystack_off() == input.len()
    }

    /// Returns true when [`Look::StartLF`] is satisfied `at` the given
    /// position in `haystack`.
    ///
    /// # Panics
    ///
    /// This may panic when `at > haystack.len()`. Note that `at ==
    /// haystack.len()` is legal and guaranteed not to panic.
    #[inline]
    pub fn is_start_lf(&self, prev_haystack: &[u8], input: &Input, at: usize) -> bool {
        prev_byte(prev_haystack, input, at).map_or(true, |byte| byte == self.lineterm.0)
    }

    /// Returns true when [`Look::EndLF`] is satisfied `at` the given position
    /// in `haystack`.
    ///
    /// # Panics
    ///
    /// This may panic when `at > haystack.len()`. Note that `at ==
    /// haystack.len()` is legal and guaranteed not to panic.
    #[inline]
    pub fn is_end_lf(&self, input: &mut Input, at: usize) -> bool {
        get_byte(input, at).map_or(true, |byte| byte == self.lineterm.0)
    }

    /// Returns true when [`Look::StartCRLF`] is satisfied `at` the given
    /// position in `haystack`.
    ///
    /// # Panics
    ///
    /// This may panic when `at > haystack.len()`. Note that `at ==
    /// haystack.len()` is legal and guaranteed not to panic.
    #[inline]
    pub fn is_start_crlf(&self, prev_haystack: &[u8], input: &mut Input, at: usize) -> bool {
        let Some(prev) = prev_byte(prev_haystack, input, at) else { return true };
        prev == b'\n' || prev == b'\r' && input.haystack().get(at).map_or(true, |&it| it != b'\r')
    }

    /// Returns true when [`Look::EndCRLF`] is satisfied `at` the given
    /// position in `haystack`.
    ///
    /// # Panics
    ///
    /// This may panic when `at > haystack.len()`. Note that `at ==
    /// haystack.len()` is legal and guaranteed not to panic.
    #[inline]
    pub fn is_end_crlf(&self, prev_haystack: &[u8], input: &mut Input, at: usize) -> bool {
        let Some(byte) = get_byte(input, at) else { return true };
        byte == b'\r'
            || byte == b'\n'
                && prev_byte(prev_haystack, &input, at).map_or(true, |byte| byte != b'\r')
    }

    /// Returns true when [`Look::WordAscii`] is satisfied `at` the given
    /// position in `haystack`.
    ///
    /// # Panics
    ///
    /// This may panic when `at > haystack.len()`. Note that `at ==
    /// haystack.len()` is legal and guaranteed not to panic.
    #[inline]
    pub fn is_word_ascii(&self, prev_haystack: &[u8], input: &mut Input, at: usize) -> bool {
        let word_before = prev_byte(prev_haystack, input, at).map_or(false, is_word_byte);
        let word_after = get_byte(input, at).map_or(false, is_word_byte);
        word_before != word_after
    }

    /// Returns true when [`Look::WordAsciiNegate`] is satisfied `at` the given
    /// position in `haystack`.
    ///
    /// # Panics
    ///
    /// This may panic when `at > haystack.len()`. Note that `at ==
    /// haystack.len()` is legal and guaranteed not to panic.
    #[inline]
    pub fn is_word_ascii_negate(&self, prev_haystack: &[u8], input: &mut Input, at: usize) -> bool {
        !self.is_word_ascii(prev_haystack, input, at)
    }

    /// Returns true when [`Look::WordUnicode`] is satisfied `at` the given
    /// position in `haystack`.
    ///
    /// # Panics
    ///
    /// This may panic when `at > haystack.len()`. Note that `at ==
    /// haystack.len()` is legal and guaranteed not to panic.
    ///
    /// # Errors
    ///
    /// This returns an error when Unicode word boundary tables
    /// are not available. Specifically, this only occurs when the
    /// `unicode-word-boundary` feature is not enabled.
    #[inline]
    pub fn is_word_unicode(
        &self,
        prev_haystack: &[u8],
        input: &mut Input,
        at: usize,
    ) -> Result<bool, UnicodeWordBoundaryError> {
        let word_before = is_word_char::rev(prev_haystack, input, at)?;
        let word_after = is_word_char::fwd(input, at)?;
        Ok(word_before != word_after)
    }

    /// Returns true when [`Look::WordUnicodeNegate`] is satisfied `at` the
    /// given position in `haystack`.
    ///
    /// # Panics
    ///
    /// This may panic when `at > haystack.len()`. Note that `at ==
    /// haystack.len()` is legal and guaranteed not to panic.
    ///
    /// # Errors
    ///
    /// This returns an error when Unicode word boundary tables
    /// are not available. Specifically, this only occurs when the
    /// `unicode-word-boundary` feature is not enabled.
    #[inline]
    pub fn is_word_unicode_negate(
        &self,
        prev_haystack: &[u8],
        input: &mut Input,
        at: usize,
    ) -> Result<bool, UnicodeWordBoundaryError> {
        // This is pretty subtle. Why do we need to do UTF-8 decoding here?
        // Well... at time of writing, the is_word_char_{fwd,rev} routines will
        // only return true if there is a valid UTF-8 encoding of a "word"
        // codepoint, and false in every other case (including invalid UTF-8).
        // This means that in regions of invalid UTF-8 (which might be a
        // subset of valid UTF-8!), it would result in \B matching. While this
        // would be questionable in the context of truly invalid UTF-8, it is
        // *certainly* wrong to report match boundaries that split the encoding
        // of a codepoint. So to work around this, we ensure that we can decode
        // a codepoint on either side of `at`. If either direction fails, then
        // we don't permit \B to match at all.
        //
        // Now, this isn't exactly optimal from a perf perspective. We could
        // try and detect this in is_word_char::{fwd,rev}, but it's not clear
        // if it's worth it. \B is, after all, rarely used. Even worse,
        // is_word_char::{fwd,rev} could do its own UTF-8 decoding, and so this
        // will wind up doing UTF-8 decoding twice. Owch. We could fix this
        // with more code complexity, but it just doesn't feel worth it for \B.
        //
        // And in particular, we do *not* have to do this with \b, because \b
        // *requires* that at least one side of `at` be a "word" codepoint,
        // which in turn implies one side of `at` must be valid UTF-8. This in
        // turn implies that \b can never split a valid UTF-8 encoding of a
        // codepoint. In the case where one side of `at` is truly invalid UTF-8
        // and the other side IS a word codepoint, then we want \b to match
        // since it represents a valid UTF-8 boundary. It also makes sense. For
        // example, you'd want \b\w+\b to match 'abc' in '\xFFabc\xFF'.
        //
        // Note also that this is not just '!is_word_unicode(..)' like it is
        // for the ASCII case. For example, neither \b nor \B is satisfied
        // within invalid UTF-8 sequences.
        let word_before = !self.is_start(&input, at)
            && match decode_last(prev_haystack, input, at) {
                None | Some(Err(_)) => return Ok(false),
                Some(Ok(_)) => is_word_char::rev(prev_haystack, input, at)?,
            };
        let word_after = !self.is_end(&input, at)
            && match decode(input, at) {
                None | Some(Err(_)) => return Ok(false),
                Some(Ok(_)) => is_word_char::fwd(input, at)?,
            };
        Ok(word_before == word_after)
    }
}

impl Default for LookMatcher {
    fn default() -> LookMatcher {
        LookMatcher::new()
    }
}

mod is_word_char {
    use regex_syntax::try_is_word_character;

    use crate::util::{decode, decode_last};
    use crate::Input;

    pub(super) fn check() -> Result<(), super::UnicodeWordBoundaryError> {
        Ok(())
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(super) fn fwd(
        input: &mut Input,
        at: usize,
    ) -> Result<bool, super::UnicodeWordBoundaryError> {
        Ok(match decode(input, at) {
            None | Some(Err(_)) => false,
            Some(Ok(ch)) => try_is_word_character(ch).expect(
                "since unicode-word-boundary, syntax and unicode-perl \
                 are all enabled, it is expected that \
                 try_is_word_character succeeds",
            ),
        })
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(super) fn rev(
        prev_haystack: &[u8],
        input: &mut Input,
        at: usize,
    ) -> Result<bool, super::UnicodeWordBoundaryError> {
        Ok(match decode_last(prev_haystack, input, at) {
            None | Some(Err(_)) => false,
            Some(Ok(ch)) => try_is_word_character(ch).expect(
                "since unicode-word-boundary, syntax and unicode-perl \
                 are all enabled, it is expected that \
                 try_is_word_character succeeds",
            ),
        })
    }
}
