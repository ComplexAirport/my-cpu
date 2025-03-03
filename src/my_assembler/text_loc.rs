/// This struct stores:
/// - the source file (or other source) of a text
/// - the contents of it
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Source {
    pub from: String,
    pub content: Vec<char>,
}

impl Source {
    pub fn new<S: Into<String>, C: AsRef<str>>(from: S, content: C) -> Self {
        Self { from: from.into(), content: content.as_ref().chars().collect() }
    }
}

/// This struct represents a location of a character in a source \
/// For instance, let's say we have a python3 code:
/// ```python3
/// def main():
///     pass
/// if __name__ == '__main__':
///     main()
/// ```
///
/// We can create a [`CharLoc`] which points to ":" symbol on first line
/// ```plain
/// 1. def main():
///              ^ our CharLoc
/// ```
/// This will allow us to access the index, column (index of that character in that line), line number.
/// We can also increment the pointer. The object will automatically change line number, column, etc.
/// based on the [`Source`] it has.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CharLoc<'a> {
    source: &'a Source,
    idx: usize,
    line: usize,
    col: usize,
}

impl<'a> CharLoc<'a> {
    pub fn from(source: &'a Source) -> Self {
        Self {
            source,
            idx: 0,
            line: 1,
            col: 0,
        }
    }

    /// Increments the pointer
    /// - Automatically adjusts the line number, column, index, etc.
    /// - If we try to increment while pointing at the last character,
    ///     the next time we call [`ch()`] method it will return None
    /// - If it meets a new line character,
    pub fn inc(&mut self, n: usize) {
        let mut i: usize = 0;
        // We will use `i` to skip over new lines
        // When we meet a '\n', we will not increment the `i`,
        // So actually we will do (`n` + newline_count) increments to
        while i < n {
            self.idx += 1;

            match self.ch() {
                Some('\n') => {
                    self.col = 0;
                    self.line += 1;
                    // Do not increment `i` here
                },

                Some(_) => {
                    self.col += 1;
                    i += 1;
                }

                None => break,
            }
        }
    }
    
    // /// Decrements the pointer
    // /// - Automatically adjusts the line number, column, index, etc.
    // /// - If we try to decrement while pointing at the first character,
    // ///     nothing will happen
    // pub fn dec(&mut self, n: isize) {
    //
    // }

    /// Returns the character the object is currently pointing to
    pub fn ch(&self) -> Option<char> {
        self.at(self.idx)
    }

    /// Returns the next character (if exists)
    pub fn next_ch(&self, n: usize) -> Option<char> {
        self.at(self.idx + n)
    }

    /// Returns the slice of `n` characters starting from current
    pub fn get_chars(&self, n: usize) -> Option<&[char]> {
        if self.idx + n < self.source.content.len() {
            Some(&self.source.content[self.idx..self.idx + n])
        } else {
            None
        }
    }

    /// Returns the character at `idx` if `idx` is valid, `None` otherwise
    pub fn at(&self, idx: usize) -> Option<char> {
        if idx < self.source.content.len() {
            Some(self.source.content[idx])
        } else {
            None
        }
    }


    /** Getter methods */
    pub fn get_idx(&self) -> usize {
        self.idx
    }

    pub fn get_col(&self) -> usize {
        self.col
    }

    pub fn get_line(&self) -> usize {
        self.line
    }
}


/// Returns a pretty representation of [`CharLoc`] \
/// Mainly for debugging purposes and error messages
pub fn pretty_loc(loc: &CharLoc) -> String {
    if let Some(ch) = loc.ch() {
        format!(
            "[{0} {1}:{2} at {3}{ch}{3}]",
            loc.source.from,
            loc.line,
            loc.col,
            if ch == '\'' { '"' } else { '\'' } // Enclose with " if char is ', enclose with ' otherwise
        )
    } else {
        format!(
            "[{0} {1}:{2}]",
            loc.source.from,
            loc.line,
            loc.col,
        )
    }
}

impl std::fmt::Debug for CharLoc<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", pretty_loc(&self))
    }
}
