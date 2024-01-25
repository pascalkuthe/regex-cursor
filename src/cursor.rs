pub trait IntoCursor {
    type Cursor: Cursor;
    fn into_cursor(self) -> Self::Cursor;
}

impl<C: Cursor> IntoCursor for C {
    type Cursor = Self;

    fn into_cursor(self) -> Self {
        self
    }
}

/// A cursor that allows transeversing a discontigous string like a rope.
pub trait Cursor {
    /// Returns the current chunk. If [`utf8_aware`](Cursor::utf8_aware) returns true then this function
    /// must **never** return a chunk that splits a unicode codepoint.
    /// See [`utf8_aware`](Cursor::utf8_aware) for details.
    ///
    /// Must never return an empty byteslice unless the underlying collection is empty.
    fn chunk(&self) -> &[u8];
    /// Whether this cursor is aware of utf-8 codepoint boundaries.
    ///
    /// **`true`** means that his cursor must never slpit a unicode codepoint at a
    ///  chunk boundary. In that case all regex features are supported.
    ///
    /// **`false`** means that his cursor can not be used for utf-8 mode
    /// matching (only affects empty strings) and can not be used to match
    /// unicode word boundaries.
    fn utf8_aware(&self) -> bool {
        true
    }
    /// Advances the cursor to the next chunk if possible. In that case `true`
    /// must be returned If the end of data is reached this function should
    /// return `false` and **not change the chunk**
    fn advance(&mut self) -> bool;
    /// Moves the cursor to the previous chunk if possible. In that case `true`
    /// must be returned If the start of data is reached this function should
    /// return `false` and **not change the chunk**
    fn backtrack(&mut self) -> bool;
    /// Returns the total length of the data. This does not
    /// take the current cursor position into account and should
    /// not change with calls to [`advance`](Cursor::advance) and [`backtrack`](Cursor::backtrack).
    fn total_bytes(&self) -> Option<usize>;
    /// The offset of the current chunk from the start of the haystack in bytes
    fn offset(&self) -> usize;
}

impl<C: Cursor> Cursor for &mut C {
    fn chunk(&self) -> &[u8] {
        C::chunk(self)
    }

    fn utf8_aware(&self) -> bool {
        C::utf8_aware(self)
    }

    fn advance(&mut self) -> bool {
        C::advance(self)
    }

    fn backtrack(&mut self) -> bool {
        C::backtrack(self)
    }

    fn total_bytes(&self) -> Option<usize> {
        C::total_bytes(self)
    }

    fn offset(&self) -> usize {
        C::offset(self)
    }
}

impl Cursor for &[u8] {
    fn chunk(&self) -> &[u8] {
        self
    }

    // true since there are no chunk bounderies
    fn utf8_aware(&self) -> bool {
        true
    }

    fn advance(&mut self) -> bool {
        false
    }

    fn backtrack(&mut self) -> bool {
        false
    }

    fn total_bytes(&self) -> Option<usize> {
        Some(self.len())
    }
    fn offset(&self) -> usize {
        0
    }
}

impl Cursor for &str {
    fn chunk(&self) -> &[u8] {
        self.as_bytes()
    }

    // true since there are no chunk bounderies
    fn utf8_aware(&self) -> bool {
        true
    }

    fn advance(&mut self) -> bool {
        false
    }

    fn backtrack(&mut self) -> bool {
        false
    }
    fn total_bytes(&self) -> Option<usize> {
        Some(<str>::len(self))
    }

    fn offset(&self) -> usize {
        0
    }
}

#[cfg(feature = "ropey")]
#[derive(Clone, Copy)]
enum Pos {
    ChunkStart,
    ChunkEnd,
}

#[cfg(feature = "ropey")]
#[derive(Clone)]
pub struct RopeyCursor<'a> {
    iter: ropey::iter::Chunks<'a>,
    current: &'a [u8],
    pos: Pos,
    len: usize,
    offset: usize,
}

#[cfg(feature = "ropey")]
impl<'a> RopeyCursor<'a> {
    pub fn new(slice: ropey::RopeSlice<'a>) -> Self {
        let iter = slice.chunks();
        let mut res =
            Self { current: &[], iter, pos: Pos::ChunkEnd, len: slice.len_bytes(), offset: 0 };
        res.advance();
        res
    }

    pub fn at(slice: ropey::RopeSlice<'a>, at: usize) -> Self {
        let (iter, offset, _, _) = slice.chunks_at_char(at);
        let mut res =
            Self { current: &[], iter, pos: Pos::ChunkEnd, len: slice.len_bytes(), offset };
        res.advance();
        res
    }
}

#[cfg(feature = "ropey")]
impl Cursor for RopeyCursor<'_> {
    fn chunk(&self) -> &[u8] {
        self.current
    }

    fn advance(&mut self) -> bool {
        match self.pos {
            Pos::ChunkStart => {
                self.iter.next();
                self.pos = Pos::ChunkEnd;
            }
            Pos::ChunkEnd => (),
        }
        for next in self.iter.by_ref() {
            if next.is_empty() {
                continue;
            }
            self.offset += self.current.len();
            self.current = next.as_bytes();
            return true;
        }
        false
    }

    fn backtrack(&mut self) -> bool {
        match self.pos {
            Pos::ChunkStart => {}
            Pos::ChunkEnd => {
                self.iter.prev();
                self.pos = Pos::ChunkStart;
            }
        }
        while let Some(prev) = self.iter.prev() {
            if prev.is_empty() {
                continue;
            }
            self.offset -= prev.len();
            self.current = prev.as_bytes();
            return true;
        }
        false
    }

    fn utf8_aware(&self) -> bool {
        true
    }

    fn total_bytes(&self) -> Option<usize> {
        Some(self.len)
    }

    fn offset(&self) -> usize {
        self.offset
    }
}

#[cfg(feature = "ropey")]
impl<'a> IntoCursor for ropey::RopeSlice<'a> {
    type Cursor = RopeyCursor<'a>;

    fn into_cursor(self) -> Self::Cursor {
        RopeyCursor::new(self)
    }
}

#[cfg(feature = "ropey")]
impl<'a> IntoCursor for &'a ropey::Rope {
    type Cursor = RopeyCursor<'a>;

    fn into_cursor(self) -> Self::Cursor {
        RopeyCursor::new(self.slice(..))
    }
}
#[cfg(all(feature = "ropey", test))]
mod ropey_test {
    use ropey::Rope;

    use crate::cursor::IntoCursor;
    use crate::Cursor;

    #[test]
    fn smoke_test() {
        let rope = Rope::from_str("abc");
        let mut cursor = rope.into_cursor();
        assert_eq!(cursor.chunk(), "abc".as_bytes());
        assert!(!cursor.advance());
        assert_eq!(cursor.chunk(), "abc".as_bytes());
        assert!(!cursor.backtrack());
        assert_eq!(cursor.chunk(), "abc".as_bytes());
        let rope = Rope::from("abc".repeat(5000));
        let mut cursor = rope.into_cursor();
        let mut offset = 0;
        loop {
            assert_eq!(cursor.offset(), offset);
            offset += cursor.chunk().len();
            if !cursor.advance() {
                break;
            }
        }
        loop {
            offset -= cursor.chunk().len();
            assert_eq!(cursor.offset(), offset);
            if !cursor.backtrack() {
                break;
            }
        }
        assert_eq!(cursor.offset(), 0);
        assert_eq!(offset, 0);
    }
}
