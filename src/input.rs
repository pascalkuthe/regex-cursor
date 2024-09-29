/*!
Types and routines that support the search APIs of most regex engines.

This sub-module isn't exposed directly, but rather, its contents are exported
at the crate root due to the universality of most of the types and routines in
this module.
*/

use std::ops::RangeBounds;

use regex_automata::{Anchored, Span};

use crate::cursor::{Cursor, IntoCursor};
use crate::util::utf8::is_boundary;

const MAX_CODEPOINT_LEN: usize = 4;

#[derive(Clone)]
pub struct Input<C: Cursor> {
    // span: Span,
    anchored: Anchored,
    earliest: bool,
    /// Position within the current chunk
    pub(crate) chunk_pos: usize,
    span: Span,
    pub(crate) slice_span: Span,
    look_behind_len: usize,
    /// the last 4 bytes before the current chunk
    look_around: [u8; MAX_CODEPOINT_LEN * 2],
    cursor: C,
}

impl<C: Cursor> Input<C> {
    /// Create a new search configuration for the given cursor.
    #[inline]
    pub fn new<T: IntoCursor<Cursor = C>>(cursor: T) -> Self {
        let cursor = cursor.into_cursor();
        let end = cursor.total_bytes().unwrap_or(usize::MAX);
        let start = cursor.offset();
        Input {
            anchored: Anchored::No,
            earliest: false,
            chunk_pos: 0,
            cursor: cursor.into_cursor(),
            // init with invalid utf8. We don't need to track
            // which of these have been filed since we only look
            // behind more than one byte in utf8 mode
            look_around: [255; 8],
            span: Span { start, end },
            slice_span: Span { start: 0, end: usize::MAX },
            look_behind_len: 0,
        }
    }

    /// Return a borrow of the current underlying chunk as a slice of bytes.
    ///
    /// # Example
    ///
    /// ```
    /// use regex_cursor::Input;
    ///
    /// let input = Input::new("foobar");
    /// assert_eq!(b"foobar", input.chunk());
    /// ```
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub fn chunk(&self) -> &[u8] {
        self.cursor.chunk()
    }

    /// Return a borrow of the current underlying chunk as a slice of bytes.
    ///
    /// # Example
    ///
    /// ```
    /// use regex_cursor::Input;
    ///
    /// let input = Input::new("foobar");
    /// assert_eq!(b"foobar", input.chunk());
    /// ```
    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub fn chunk_offset(&self) -> usize {
        self.cursor.offset()
    }

    /// Return the start position of this search.
    ///
    /// This is a convenience routine for `search.get_span().start()`.
    ///
    /// When [`Input::is_done`] is `false`, this is guaranteed to return
    /// an offset that is less than or equal to [`Input::end`]. Otherwise,
    /// the offset is one greater than [`Input::end`].
    ///
    /// # Example
    ///
    /// ```
    /// use regex_automata::Input;
    ///
    /// let input = Input::new("foobar");
    /// assert_eq!(0, input.start());
    ///
    /// let input = Input::new("foobar").span(2..4);
    /// assert_eq!(2, input.start());
    /// ```
    #[inline]
    pub fn start(&self) -> usize {
        self.get_span().start
    }

    #[inline]
    pub fn clear_look_behind(&mut self) {
        self.look_around = [255; 8];
    }

    /// Return the end position of this search.
    ///
    /// This is a convenience routine for `search.get_span().end()`.
    ///
    /// This is guaranteed to return an offset that is a valid exclusive end
    /// bound for this input's haystack.
    ///
    /// # Example
    ///
    /// ```
    /// use regex_automata::Input;
    ///
    /// let input = Input::new("foobar");
    /// assert_eq!(6, input.end());
    ///
    /// let input = Input::new("foobar").span(2..4);
    /// assert_eq!(4, input.end());
    /// ```
    #[inline]
    pub fn end(&self) -> usize {
        self.span.end
    }

    #[inline(always)]
    pub fn get_chunk_end(&self) -> usize {
        let end = self.span.end - self.cursor.offset();
        end.min(self.chunk().len())
    }

    /// Return the span for this search configuration.
    ///
    /// If one was not explicitly set, then the span corresponds to the entire
    /// range of the haystack.
    ///
    /// When [`Input::is_done`] is `false`, the span returned is guaranteed
    /// to correspond to valid bounds for this input's haystack.
    ///
    /// # Example
    ///
    /// ```
    /// use regex_automata::{Input, Span};
    ///
    /// let input = Input::new("foobar");
    /// assert_eq!(Span { start: 0, end: 6 }, input.get_span());
    /// ```
    #[inline]
    pub fn get_span(&self) -> Span {
        self.span
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn set_look_behind(&mut self) {
        #[cold]
        fn copy_partial_look_behind(look_behind: &mut [u8; MAX_CODEPOINT_LEN * 2], chunk: &[u8]) {
            look_behind[..chunk.len()].copy_from_slice(chunk)
        }

        let chunk = self.cursor.chunk();
        let len = chunk.len();
        if len < MAX_CODEPOINT_LEN {
            copy_partial_look_behind(&mut self.look_around, chunk);
            self.look_behind_len = chunk.len();
        } else {
            self.look_behind_len = MAX_CODEPOINT_LEN;
            self.look_around[..MAX_CODEPOINT_LEN].copy_from_slice(&chunk[len - MAX_CODEPOINT_LEN..])
        }
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn advance(&mut self) -> bool {
        let old_len = self.cursor.chunk().len();
        let advanced = self.cursor.advance();
        if advanced {
            self.chunk_pos = 0;
        } else if self.span.end > self.cursor.offset() + old_len {
            self.span.end = self.cursor.offset() + old_len;
        }
        advanced
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn advance_with_look_behind(&mut self) -> bool {
        self.set_look_behind();
        self.advance()
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn backtrack(&mut self) -> bool {
        let backtracked = self.cursor.backtrack();
        if backtracked {
            self.chunk_pos = self.chunk().len();
        } else if self.cursor.offset() != 0 {
            unreachable!("cursor does not support backtracking {}", self.cursor.offset())
        }
        backtracked
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn ensure_look_behind(&mut self) -> Option<u8> {
        let look_behind = if self.chunk_pos == 0 {
            // move back to the last chunk to read the look behind
            if self.slice_span.start != self.chunk_offset() && self.backtrack() {
                self.advance_with_look_behind();
                Some(self.look_around[self.look_behind_len - 1])
            } else {
                self.look_behind_len = 0;
                None
            }
        } else if self.slice_span.start == self.chunk_offset() + self.chunk_pos {
            None
        } else {
            self.chunk().get(self.chunk_pos - 1).copied()
        };
        look_behind
    }

    pub fn look_around(&mut self) -> (&[u8], usize) {
        // TODO: cache look_ahead?

        let mut chunk = self.cursor.chunk();
        let end = chunk.len().min(self.slice_span.end - self.chunk_offset());
        chunk = &chunk[..end];
        if self.chunk_pos == 0 {
            #[cold]
            fn copy_partial_look_ahead(look_behind: &mut [u8], chunk: &[u8]) {
                look_behind[..chunk.len()].copy_from_slice(chunk)
            }

            let look_around_len;
            if chunk.len() < MAX_CODEPOINT_LEN {
                look_around_len = self.look_behind_len + chunk.len();
                copy_partial_look_ahead(&mut self.look_around[self.look_behind_len..], chunk);
            } else {
                look_around_len = self.look_behind_len + MAX_CODEPOINT_LEN;
                self.look_around[self.look_behind_len..look_around_len]
                    .copy_from_slice(&chunk[..MAX_CODEPOINT_LEN])
            }
            (&self.look_around[..look_around_len], self.look_behind_len)
        } else {
            (chunk, self.chunk_pos)
        }
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn chunk_pos(&self) -> usize {
        self.chunk_pos
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn set_chunk_pos(&mut self, at: usize) {
        self.chunk_pos = at;
    }

    /// Sets the anchor mode of a search.
    ///
    /// When a search is anchored (so that's [`Anchored::Yes`] or
    /// [`Anchored::Pattern`]), a match must begin at the start of a search.
    /// When a search is not anchored (that's [`Anchored::No`]), regex engines
    /// will behave as if the pattern started with a `(?:s-u.)*?`. This prefix
    /// permits a match to appear anywhere.
    ///
    /// By default, the anchored mode is [`Anchored::No`].
    ///
    /// **WARNING:** this is subtly different than using a `^` at the start of
    /// your regex. A `^` forces a regex to match exclusively at the start of
    /// a chunk, regardless of where you begin your search. In contrast,
    /// anchoring a search will allow your regex to match anywhere in your
    /// chunk, but the match must start at the beginning of a search.
    ///
    /// For example, consider the chunk `aba` and the following searches:
    ///
    /// 1. The regex `^a` is compiled with `Anchored::No` and searches `aba`
    ///    starting at position `2`. Since `^` requires the match to start at
    ///    the beginning of the chunk and `2 > 0`, no match is found.
    /// 2. The regex `a` is compiled with `Anchored::Yes` and searches `aba`
    ///    starting at position `2`. This reports a match at `[2, 3]` since
    ///    the match starts where the search started. Since there is no `^`,
    ///    there is no requirement for the match to start at the beginning of
    ///    the chunk.
    /// 3. The regex `a` is compiled with `Anchored::Yes` and searches `aba`
    ///    starting at position `1`. Since `b` corresponds to position `1` and
    ///    since the search is anchored, it finds no match. While the regex
    ///    matches at other positions, configuring the search to be anchored
    ///    requires that it only report a match that begins at the same offset
    ///    as the beginning of the search.
    /// 4. The regex `a` is compiled with `Anchored::No` and searches `aba`
    ///    startting at position `1`. Since the search is not anchored and
    ///    the regex does not start with `^`, the search executes as if there
    ///    is a `(?s:.)*?` prefix that permits it to match anywhere. Thus, it
    ///    reports a match at `[2, 3]`.
    ///
    /// Note that the [`Anchored::Pattern`] mode is like `Anchored::Yes`,
    /// except it only reports matches for a particular pattern.
    ///
    /// # Example
    ///
    /// This demonstrates the differences between an anchored search and
    /// a pattern that begins with `^` (as described in the above warning
    /// message).
    ///
    /// ```
    /// use regex_automata::{
    ///     nfa::thompson::pikevm::PikeVM,
    ///     Anchored, Match, Input,
    /// };
    ///
    /// let chunk = "aba";
    ///
    /// let re = PikeVM::new(r"^a")?;
    /// let (mut cache, mut caps) = (re.create_cache(), re.create_captures());
    /// let input = Input::new(chunk).span(2..3).anchored(Anchored::No);
    /// re.search(&mut cache, &input, &mut caps);
    /// // No match is found because 2 is not the beginning of the chunk,
    /// // which is what ^ requires.
    /// assert_eq!(None, caps.get_match());
    ///
    /// let re = PikeVM::new(r"a")?;
    /// let (mut cache, mut caps) = (re.create_cache(), re.create_captures());
    /// let input = Input::new(chunk).span(2..3).anchored(Anchored::Yes);
    /// re.search(&mut cache, &input, &mut caps);
    /// // An anchored search can still match anywhere in the chunk, it just
    /// // must begin at the start of the search which is '2' in this case.
    /// assert_eq!(Some(Match::must(0, 2..3)), caps.get_match());
    ///
    /// let re = PikeVM::new(r"a")?;
    /// let (mut cache, mut caps) = (re.create_cache(), re.create_captures());
    /// let input = Input::new(chunk).span(1..3).anchored(Anchored::Yes);
    /// re.search(&mut cache, &input, &mut caps);
    /// // No match is found since we start searching at offset 1 which
    /// // corresponds to 'b'. Since there is no '(?s:.)*?' prefix, no match
    /// // is found.
    /// assert_eq!(None, caps.get_match());
    ///
    /// let re = PikeVM::new(r"a")?;
    /// let (mut cache, mut caps) = (re.create_cache(), re.create_captures());
    /// let input = Input::new(chunk).span(1..3).anchored(Anchored::No);
    /// re.search(&mut cache, &input, &mut caps);
    /// // Since anchored=no, an implicit '(?s:.)*?' prefix was added to the
    /// // pattern. Even though the search starts at 'b', the 'match anything'
    /// // prefix allows the search to match 'a'.
    /// let expected = Some(Match::must(0, 2..3));
    /// assert_eq!(expected, caps.get_match());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn anchored(&mut self, mode: Anchored) -> &mut Self {
        self.set_anchored(mode);
        self
    }

    /// Whether to execute an "earliest" search or not.
    ///
    /// When running a non-overlapping search, an "earliest" search will return
    /// the match location as early as possible. For example, given a pattern
    /// of `foo[0-9]+` and a chunk of `foo12345`, a normal leftmost search
    /// will return `foo12345` as a match. But an "earliest" search for regex
    /// engines that support "earliest" semantics will return `foo1` as a
    /// match, since as soon as the first digit following `foo` is seen, it is
    /// known to have found a match.
    ///
    /// Note that "earliest" semantics generally depend on the regex engine.
    /// Different regex engines may determine there is a match at different
    /// points. So there is no guarantee that "earliest" matches will always
    /// return the same offsets for all regex engines. The "earliest" notion
    /// is really about when the particular regex engine determines there is
    /// a match rather than a consistent semantic unto itself. This is often
    /// useful for implementing "did a match occur or not" predicates, but
    /// sometimes the offset is useful as well.
    ///
    /// This is disabled by default.
    ///
    /// # Example
    ///
    /// This example shows the difference between "earliest" searching and
    /// normal searching.
    ///
    /// ```
    /// use regex_automata::{nfa::thompson::pikevm::PikeVM, Match, Input};
    ///
    /// let re = PikeVM::new(r"foo[0-9]+")?;
    /// let mut cache = re.create_cache();
    /// let mut caps = re.create_captures();
    ///
    /// // A normal search implements greediness like you expect.
    /// let input = Input::new("foo12345");
    /// re.search(&mut cache, &input, &mut caps);
    /// assert_eq!(Some(Match::must(0, 0..8)), caps.get_match());
    ///
    /// // When 'earliest' is enabled and the regex engine supports
    /// // it, the search will bail once it knows a match has been
    /// // found.
    /// let input = Input::new("foo12345").earliest(true);
    /// re.search(&mut cache, &input, &mut caps);
    /// assert_eq!(Some(Match::must(0, 0..4)), caps.get_match());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn earliest(&mut self, yes: bool) -> &mut Self {
        self.set_earliest(yes);
        self
    }

    /// Set the anchor mode of a search.
    ///
    /// This is like [`Input::anchored`], except it mutates the search
    /// configuration in place.
    ///
    /// # Example
    ///
    /// ```
    /// use regex_automata::{Anchored, Input, PatternID};
    ///
    /// let mut input = Input::new("foobar");
    /// assert_eq!(Anchored::No, input.get_anchored());
    ///
    /// let pid = PatternID::must(5);
    /// input.set_anchored(Anchored::Pattern(pid));
    /// assert_eq!(Anchored::Pattern(pid), input.get_anchored());
    /// ```
    #[inline]
    pub fn set_anchored(&mut self, mode: Anchored) {
        self.anchored = mode;
    }

    /// Set whether the search should execute in "earliest" mode or not.
    ///
    /// This is like [`Input::earliest`], except it mutates the search
    /// configuration in place.
    ///
    /// # Example
    ///
    /// ```
    /// use regex_automata::Input;
    ///
    /// let mut input = Input::new("foobar");
    /// assert!(!input.get_earliest());
    /// input.set_earliest(true);
    /// assert!(input.get_earliest());
    /// ```
    #[inline]
    pub fn set_earliest(&mut self, yes: bool) {
        self.earliest = yes;
    }

    /// Set the span for this search.
    ///
    /// This routine does not panic if the span given is not a valid range for
    /// this search's haystack. If this search is run with an invalid range,
    /// then the most likely outcome is that the actual search execution will
    /// panic.
    ///
    /// This routine is generic over how a span is provided. While
    /// a [`Span`] may be given directly, one may also provide a
    /// `std::ops::Range<usize>`. To provide anything supported by range
    /// syntax, use the [`Input::range`] method.
    ///
    /// The default span is the entire haystack.
    ///
    /// Note that [`Input::range`] overrides this method and vice versa.
    ///
    /// # Panics
    ///
    /// This panics if the given span does not correspond to valid bounds in
    /// the haystack or the termination of a search.
    ///
    /// # Example
    ///
    /// This example shows how the span of the search can impact whether a
    /// match is reported or not. This is particularly relevant for look-around
    /// operators, which might take things outside of the span into account
    /// when determining whether they match.
    ///
    /// ```
    /// # if cfg!(miri) { return Ok(()); } // miri takes too long
    /// use regex_automata::{
    ///     nfa::thompson::pikevm::PikeVM,
    ///     Match, Input,
    /// };
    ///
    /// // Look for 'at', but as a distinct word.
    /// let re = PikeVM::new(r"\bat\b")?;
    /// let mut cache = re.create_cache();
    /// let mut caps = re.create_captures();
    ///
    /// // Our haystack contains 'at', but not as a distinct word.
    /// let haystack = "batter";
    ///
    /// // A standard search finds nothing, as expected.
    /// let input = Input::new(haystack);
    /// re.search(&mut cache, &input, &mut caps);
    /// assert_eq!(None, caps.get_match());
    ///
    /// // But if we wanted to search starting at position '1', we might
    /// // slice the haystack. If we do this, it's impossible for the \b
    /// // anchors to take the surrounding context into account! And thus,
    /// // a match is produced.
    /// let input = Input::new(&haystack[1..3]);
    /// re.search(&mut cache, &input, &mut caps);
    /// assert_eq!(Some(Match::must(0, 0..2)), caps.get_match());
    ///
    /// // But if we specify the span of the search instead of slicing the
    /// // haystack, then the regex engine can "see" outside of the span
    /// // and resolve the anchors correctly.
    /// let input = Input::new(haystack).span(1..3);
    /// re.search(&mut cache, &input, &mut caps);
    /// assert_eq!(None, caps.get_match());
    ///
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    ///
    /// This may seem a little ham-fisted, but this scenario tends to come up
    /// if some other regex engine found the match span and now you need to
    /// re-process that span to look for capturing groups. (e.g., Run a faster
    /// DFA first, find a match, then run the PikeVM on just the match span to
    /// resolve capturing groups.) In order to implement that sort of logic
    /// correctly, you need to set the span on the search instead of slicing
    /// the haystack directly.
    ///
    /// The other advantage of using this routine to specify the bounds of the
    /// search is that the match offsets are still reported in terms of the
    /// original haystack. For example, the second search in the example above
    /// reported a match at position `0`, even though `at` starts at offset
    /// `1` because we sliced the haystack.
    #[inline]
    pub fn span<S: Into<Span>>(&mut self, span: S) -> &mut Input<C> {
        self.set_span(span);
        self
    }

    /// Set the starting offset for the span for this search configuration.
    ///
    /// This is a convenience routine for only mutating the start of a span
    /// without having to set the entire span.
    ///
    /// # Panics
    ///
    /// This panics if the span resulting from the new start position does not
    /// correspond to valid bounds in the haystack or the termination of a
    /// search.
    ///
    #[inline]
    pub fn set_start(&mut self, start: usize) {
        self.set_span(Span { start, ..self.get_span() });
    }

    /// Set the ending offset for the span for this search configuration.
    ///
    /// This is a convenience routine for only mutating the end of a span
    /// without having to set the entire span.
    ///
    /// # Panics
    ///
    /// This panics if the span resulting from the new end position does not
    /// correspond to valid bounds in the haystack or the termination of a
    /// search.
    #[inline]
    pub fn set_end(&mut self, end: usize) {
        self.set_span(Span { end, ..self.get_span() });
    }

    /// Like `Input::span`, but accepts any range instead.
    ///
    /// This routine does not panic if the range given is not a valid range for
    /// this search's haystack. If this search is run with an invalid range,
    /// then the most likely outcome is that the actual search execution will
    /// panic.
    ///
    /// The default range is the entire haystack.
    ///
    /// Note that [`Input::span`] overrides this method and vice versa.
    ///
    /// # Panics
    ///
    /// This routine will panic if the given range could not be converted
    /// to a valid [`Range`]. For example, this would panic when given
    /// `0..=usize::MAX` since it cannot be represented using a half-open
    /// interval in terms of `usize`.
    ///
    /// This also panics if the given range does not correspond to valid bounds
    /// in the haystack or the termination of a search.
    ///
    /// # Example
    ///
    /// ```
    /// use regex_automata::Input;
    ///
    /// let input = Input::new("foobar");
    /// assert_eq!(0..6, input.get_range());
    ///
    /// let input = Input::new("foobar").range(2..=4);
    /// assert_eq!(2..5, input.get_range());
    /// ```
    #[inline]
    pub fn range<R: RangeBounds<usize>>(mut self, range: R) -> Input<C> {
        self.set_range(range);
        self
    }

    /// Set the span for this search configuration.
    ///
    /// This is like the [`Input::span`] method, except this mutates the
    /// span in place.
    ///
    /// This routine is generic over how a span is provided. While
    /// a [`Span`] may be given directly, one may also provide a
    /// `std::ops::Range<usize>`.
    ///
    /// # Panics
    ///
    /// This panics if the given span does not correspond to valid bounds in
    /// the haystack or the termination of a search.
    ///
    /// # Example
    ///
    /// ```
    /// use regex_automata::Input;
    ///
    /// let mut input = Input::new("foobar");
    /// assert_eq!(0..6, input.get_range());
    /// input.set_span(2..4);
    /// assert_eq!(2..4, input.get_range());
    /// ```
    #[inline]
    pub fn set_span<S: Into<Span>>(&mut self, span: S) {
        let span = span.into();
        assert!(span.start <= span.end.saturating_add(1), "invalid span {:?}", span,);
        if self.at() < span.start {
            self.move_to(span.start);
        } else if !self.is_done() && self.at() > span.end {
            self.move_to(span.end);
        }
        self.span = span;
    }

    #[inline]
    pub fn slice_span<S: Into<Span>>(&mut self, span: S) -> &mut Input<C> {
        let span = span.into();
        assert!(span.start <= span.end.saturating_add(1), "invalid span {:?}", span,);
        if self.at() < span.start {
            self.move_to(span.start);
        } else if !self.is_done() && self.at() > span.end {
            self.move_to(span.end);
        }
        self.slice_span = span;
        self.span = span;
        self
    }

    #[inline]
    pub fn slice<R: RangeBounds<usize>>(&mut self, range: R) -> &mut Input<C> {
        use core::ops::Bound;

        // It's a little weird to convert ranges into spans, and then spans
        // back into ranges when we actually slice the haystack. Because
        // of that process, we always represent everything as a half-open
        // internal. Therefore, handling things like m..=n is a little awkward.
        let start = match range.start_bound() {
            Bound::Included(&i) => i,
            // Can this case ever happen? Range syntax doesn't support it...
            Bound::Excluded(&i) => i.checked_add(1).unwrap(),
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(&i) => i.checked_add(1).unwrap(),
            Bound::Excluded(&i) => i,
            Bound::Unbounded => self.cursor.total_bytes().unwrap_or(usize::MAX),
        };
        self.slice_span(Span { start, end })
    }

    #[inline]
    pub(crate) fn move_to(&mut self, at: usize) {
        debug_assert!(at <= self.span.end.saturating_add(1));
        // TODO: fastpath for O(log N) chunk jumping
        while at < self.cursor.offset() {
            self.backtrack();
        }
        if at != self.cursor.offset() {
            while at >= self.cursor.offset() + self.chunk().len() {
                let advanced = self.advance();
                if !advanced {
                    let chunk_pos = (at - self.cursor.offset()).min(self.chunk().len());
                    self.set_chunk_pos(chunk_pos);
                    return;
                }
            }
        }
        self.set_chunk_pos(at - self.cursor.offset());
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn at(&self) -> usize {
        self.cursor.offset() + self.chunk_pos()
    }

    #[cfg_attr(feature = "perf-inline", inline(always))]
    pub(crate) fn with<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let anchored = self.anchored;
        let earliest = self.earliest;
        let span = self.span;
        let res = f(self);
        self.set_span(span);
        self.set_earliest(earliest);
        self.set_anchored(anchored);
        res
    }

    // #[cfg_attr(feature = "perf-inline", inline(always))]
    // pub(crate) fn try_clone(&self) -> Option<Input<C>> {
    //     let res = Input {
    //         cursor: self.cursor.try_clone()?,
    //         anchored: self.anchored,
    //         earliest: self.earliest,
    //         offset: self.offset,
    //         chunk_pos: self.chunk_pos,
    //         span: self.span,
    //         look_behind: self.look_behind,
    //     };
    //     Some(res)
    // }

    /// Set the span for this search configuration given any range.
    ///
    /// This is like the [`Input::range`] method, except this mutates the
    /// span in place.
    ///
    /// This routine does not panic if the range given is not a valid range for
    /// this search's haystack. If this search is run with an invalid range,
    /// then the most likely outcome is that the actual search execution will
    /// panic.
    ///
    /// # Panics
    ///
    /// This routine will panic if the given range could not be converted
    /// to a valid [`Range`]. For example, this would panic when given
    /// `0..=usize::MAX` since it cannot be represented using a half-open
    /// interval in terms of `usize`.
    ///
    /// This also panics if the given span does not correspond to valid bounds
    /// in the haystack or the termination of a search.
    ///
    /// # Example
    ///
    /// ```
    /// use regex_automata::Input;
    ///
    /// let mut input = Input::new("foobar");
    /// assert_eq!(0..6, input.get_range());
    /// input.set_range(2..=4);
    /// assert_eq!(2..5, input.get_range());
    /// ```
    #[inline]
    pub fn set_range<R: RangeBounds<usize>>(&mut self, range: R) {
        use core::ops::Bound;

        // It's a little weird to convert ranges into spans, and then spans
        // back into ranges when we actually slice the haystack. Because
        // of that process, we always represent everything as a half-open
        // internal. Therefore, handling things like m..=n is a little awkward.
        let start = match range.start_bound() {
            Bound::Included(&i) => i,
            // Can this case ever happen? Range syntax doesn't support it...
            Bound::Excluded(&i) => i.checked_add(1).unwrap(),
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(&i) => i.checked_add(1).unwrap(),
            Bound::Excluded(&i) => i,
            Bound::Unbounded => self.cursor.total_bytes().unwrap_or(usize::MAX),
        };
        self.set_span(Span { start, end });
    }

    /// Return the anchored mode for this search configuration.
    ///
    /// If no anchored mode was set, then it defaults to [`Anchored::No`].
    ///
    /// # Example
    ///
    /// ```
    /// use regex_automata::{Anchored, Input, PatternID};
    ///
    /// let mut input = Input::new("foobar");
    /// assert_eq!(Anchored::No, input.get_anchored());
    ///
    /// let pid = PatternID::must(5);
    /// input.set_anchored(Anchored::Pattern(pid));
    /// assert_eq!(Anchored::Pattern(pid), input.get_anchored());
    /// ```
    #[inline]
    pub fn get_anchored(&self) -> Anchored {
        self.anchored
    }

    /// Return whether this search should execute in "earliest" mode.
    ///
    /// # Example
    ///
    /// ```
    /// use regex_automata::Input;
    ///
    /// let input = Input::new("foobar");
    /// assert!(!input.get_earliest());
    /// ```
    #[inline]
    pub fn get_earliest(&self) -> bool {
        self.earliest
    }

    /// Return true if and only if this search can never return any other
    /// matches.
    ///
    /// This occurs when the start position of this search is greater than the
    /// end position of the search.
    ///
    /// # Example
    ///
    /// ```
    /// use regex_automata::Input;
    ///
    /// let mut input = Input::new("foobar");
    /// assert!(!input.is_done());
    /// input.set_start(6);
    /// assert!(!input.is_done());
    /// input.set_start(7);
    /// assert!(input.is_done());
    /// ```
    #[inline]
    pub fn is_done(&self) -> bool {
        self.get_span().start > self.get_span().end
    }

    /// Returns true if and only if the given offset in this search's chunk
    /// falls on a valid UTF-8 encoded codepoint boundary.
    ///
    /// If the chunk is not valid UTF-8, then the behavior of this routine
    /// is unspecified.
    ///
    /// # Example
    ///
    /// This shows where codepoint bounardies do and don't exist in valid
    /// UTF-8.
    ///
    /// ```
    /// use regex_automata::Input;
    ///
    /// let input = Input::new("☃");
    /// assert!(input.is_char_boundary(0));
    /// assert!(!input.is_char_boundary(1));
    /// assert!(!input.is_char_boundary(2));
    /// assert!(input.is_char_boundary(3));
    /// assert!(!input.is_char_boundary(4));
    /// ```
    #[inline]
    pub fn is_char_boundary(&mut self) -> bool {
        is_boundary(self.chunk(), self.chunk_pos)
    }
}

impl<C: Cursor> core::fmt::Debug for Input<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use regex_automata::util::escape::DebugHaystack;

        f.debug_struct("Input")
            .field("chunk", &DebugHaystack(self.chunk()))
            .field("anchored", &self.anchored)
            .field("earliest", &self.earliest)
            .field("chunk_pos", &self.chunk_pos)
            .field("chunk_offset", &self.cursor.offset())
            .field("span", &self.span)
            .finish()
    }
}
