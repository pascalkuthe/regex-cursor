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
    /// Returns the current chunk. If utf8_aware returns true then this function
    /// must **never** return a chunk that splits a unicode codepoint.
    /// See [`utf8_aware`] for details.
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
    /// not change with calls to [`advance`] and [`backtrack`].
    fn total_bytes(&self) -> Option<usize>;
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
}

#[cfg(feature = "ropey")]
impl<'a> RopeyCursor<'a> {
    pub fn new(slice: ropey::RopeSlice<'a>) -> Self {
        let mut iter = slice.chunks();
        Self {
            current: iter.next().unwrap_or_default().as_bytes(),
            iter,
            pos: Pos::ChunkEnd,
            len: slice.len_bytes(),
        }
    }
    pub fn at_char(slice: ropey::RopeSlice<'a>, at: usize) -> Self {
        let (mut iter, _, _, _) = slice.chunks_at_char(at);
        Self {
            current: iter.next().unwrap_or_default().as_bytes(),
            iter,
            pos: Pos::ChunkEnd,
            len: slice.len_bytes(),
        }
    }

    pub fn at_byte(slice: ropey::RopeSlice<'a>, at: usize) -> Self {
        let (mut iter, _, _, _) = slice.chunks_at_char(at);
        Self {
            current: iter.next().unwrap_or_default().as_bytes(),
            iter,
            pos: Pos::ChunkEnd,
            len: slice.len_bytes(),
        }
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
