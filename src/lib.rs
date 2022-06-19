use thiserror::Error as ErrorTrait;

#[derive(Debug, ErrorTrait)]
#[error("Error at byte position {byte}: {kind}")]
pub struct ParseError {
    pub byte: usize,
    pub kind: ParseErrorKind,
}

#[derive(Debug, ErrorTrait)]
pub enum ParseErrorKind {
    #[error("Unexpected end of source, which is {0} bytes")]
    UnexpectedEnd(usize),

    #[error("Expected `{0}` but got `{1}` instead")]
    UnexpectedString(String, String),

    #[error("Expected identifier but got `{0}` instead")]
    InvalidIdentifier(String),

    #[error("Expected end of source, which is {0} bytes")]
    NotFinished(usize),

    #[error("Mismatched `{opener}`, expected matching closer but found `{found}` instead")]
    MismatchedParen { opener: String, found: String },
}

type Error = ParseError;
type Kind = ParseErrorKind;
type Result<T> = std::result::Result<T, Error>;

/// A trait that can be implemented to customize a `Parser`.
pub trait ParserRules: Clone {
    /// The sequence of bytes that prefixes a single-line comment.
    const SINGLE_LINE_COMMENT: Option<&'static [u8]> = Some(b"//");

    /// A pair of opening and closing multi-line comment tokens.
    const MULTI_LINE_COMMENT: Option<(&'static [u8], &'static [u8])> = Some((b"/*", b"*/"));

    /// A list of paired parentheses which can be nested.
    const NESTABLE_PARENS: &'static [(u8, u8)] =
        &[(b'{', b'}'), (b'[', b']'), (b'(', b')'), (b'<', b'>')];

    /// A list of paired parentheses which cannot be nested - for example, quotes.
    const NON_NESTABLE_PARENS: &'static [(u8, u8)] = &[(b'"', b'"'), (b'\'', b'\'')];

    /// If `true`, whitespace is skipped after every parsing function.
    fn always_skip_whitespace() -> bool {
        true
    }

    /// Test whether a byte is whitespace.
    fn is_whitespace_byte(ch: u8) -> bool {
        matches!(ch, b' ' | b'\n' | b'\r' | b'\t')
    }

    /// Test whether a byte can be the beginning of an identifier.
    fn is_ident_start_byte(ch: u8) -> bool {
        ch == b'_' || (b'a'..=b'z').contains(&ch) || (b'A'..=b'Z').contains(&ch)
    }

    /// Test whether a byte can be within an identifies.
    fn is_ident_byte(ch: u8) -> bool {
        ch == b'_'
            || (b'a'..=b'z').contains(&ch)
            || (b'A'..=b'Z').contains(&ch)
            || (b'0'..=b'9').contains(&ch)
    }
}

/// The default `Parser` rules - including Rust-style comments and identifiers.
#[derive(Clone, Copy)]
pub struct DefaultRules;

/// Like `DefaultRules`, except newlines are not considered whitespace and will not be skipped
/// over.
#[derive(Clone, Copy)]
pub struct LineBasedRules;

/// Like `DefaultRules`, except whitespace is never skipped automatically.
#[derive(Clone, Copy)]
pub struct ExactRules;

impl ParserRules for DefaultRules {}

impl ParserRules for LineBasedRules {
    fn is_whitespace_byte(ch: u8) -> bool {
        matches!(ch, b' ' | b'\r' | b'\t')
    }
}

impl ParserRules for ExactRules {
    fn always_skip_whitespace() -> bool {
        false
    }
}

pub type DefaultParser<'a> = Parser<'a, DefaultRules>;
pub type ExactParser<'a> = Parser<'a, ExactRules>;

/// A struct for parsing a given input.
///
/// The generic type parameter `R` determines the rules for parsing. The `Parser` also stores a
/// view into the source to be parsed, and its various methods return slices of that same source.
#[derive(Clone, PartialEq, Eq)]
pub struct Parser<'a, R: ParserRules = DefaultRules> {
    source: &'a [u8],
    cursor: usize,
    _phantom: std::marker::PhantomData<R>,
}

impl<'a, R: ParserRules> Parser<'a, R> {
    /// Start parsing a string.
    pub fn new(source: &'a str) -> Self {
        Self::new_from_bytes(source.as_bytes())
    }

    /// Start parsing some bytes.
    pub fn new_from_bytes(source: &'a [u8]) -> Self {
        Parser {
            source: source,
            cursor: 0,
            _phantom: std::marker::PhantomData,
        }
    }

    /// Clone the parser, but with a different set of rules.
    pub fn clone_with_rules<N: ParserRules>(&self) -> Parser<'a, N> {
        Parser {
            source: self.source,
            cursor: self.cursor,
            _phantom: std::marker::PhantomData,
        }
    }

    /// Return an immutable reference to this parser, but with a different set of rules.
    pub fn with_rules<N: ParserRules>(&self) -> &Parser<'a, N> {
        unsafe { std::mem::transmute(self) }
    }

    /// Return a mutable reference to this parser, but with a different set of rules.
    pub fn with_rules_mut<N: ParserRules>(&mut self) -> &mut Parser<'a, N> {
        unsafe { std::mem::transmute(self) }
    }

    /// Return a reference to the underlying source.
    ///
    /// # Panics
    /// Panics if the source is not valid UTF-8.
    #[inline(always)]
    pub fn source(&self) -> &'a str {
        std::str::from_utf8(self.source).expect("Parser `source` must be valid UTF-8")
    }

    /// Return a reference to the underlying source bytes.
    #[inline(always)]
    pub fn bytes(&self) -> &'a [u8] {
        self.source
    }

    /// Returns the length of the source.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.bytes().len()
    }

    /// Returns the number of bytes that have already been parsed.
    #[inline(always)]
    pub fn cursor(&self) -> usize {
        self.cursor
    }

    /// Returns whether there are any more bytes left or not.
    #[inline(always)]
    pub fn finished(&self) -> bool {
        self.cursor() == self.bytes().len()
    }

    /// Returns an error if the parser is not finished.
    pub fn expect_finished(&self) -> Result<()> {
        if !self.finished() {
            return Err(Error {
                byte: self.cursor(),
                kind: Kind::NotFinished(self.len()),
            });
        }

        Ok(())
    }

    /// Returns an error if the parser is finished.
    pub fn expect_not_finished(&self) -> Result<()> {
        if self.finished() {
            return Err(Error {
                byte: self.cursor(),
                kind: Kind::UnexpectedEnd(self.len()),
            });
        }

        Ok(())
    }

    /// Move the cursor forward `n` bytes, and possibly skips whitespace depending on rules.
    ///
    /// # Panics
    /// Panics if the cursor passes the end of the source.
    pub fn skip_n_unchecked(&mut self, n: usize) -> &'a [u8] {
        let start = self.cursor();
        self.cursor += n;
        let result = &self.bytes()[start..self.cursor()];
        self.maybe_skip_whitespace();
        result
    }

    /// Move the cursor forward `n` bytes, and possibly skips whitespace depending on rules.
    ///
    /// # Errors
    /// Returns an error if the cursor passes the end of the source. Does not modify the cursor in
    /// this case.
    pub fn skip_n(&mut self, n: usize) -> Result<&'a [u8]> {
        match self.cursor() + n <= self.len() {
            true => Ok(self.skip_n_unchecked(n)),
            false => Err(Error {
                byte: self.cursor(),
                kind: Kind::UnexpectedEnd(self.len()),
            }),
        }
    }

    /// Returns all successive whitespace (and comments), if any, without moving the cursor.
    pub fn check_whitespace(&mut self) -> Option<&'a [u8]> {
        let start = self.cursor();
        let mut cur = start;
        let mut in_comment = false;
        let mut comment_nesting = 0;
        loop {
            let mut close_comment = false;

            if in_comment {
                if comment_nesting == 0 && (cur == self.len() || self.bytes()[cur] == b'\n') {
                    close_comment = true;
                }
            } else {
                if let Some(comment_start) = R::SINGLE_LINE_COMMENT {
                    if self.check_from(cur, comment_start).is_some() {
                        in_comment = true;
                        cur += comment_start.len() - 1;
                    }
                }
            }

            if !in_comment || comment_nesting > 0 {
                if let Some((opener, closer)) = R::MULTI_LINE_COMMENT {
                    if self.check_from(cur, opener).is_some() {
                        in_comment = true;
                        comment_nesting += 1;
                        cur += opener.len() - 1;
                    }

                    if self.check_from(cur, closer).is_some() && in_comment {
                        comment_nesting -= 1;
                        if comment_nesting == 0 {
                            close_comment = true;
                        }
                        cur += closer.len() - 1;
                    }
                }
            }

            if cur == self.len() || !(in_comment || R::is_whitespace_byte(self.bytes()[cur])) {
                break;
            }

            cur += 1;
            if close_comment {
                in_comment = false;
            }
        }

        let whitespace = &self.bytes()[start..cur];
        match whitespace.len() {
            0 => None,
            _ => Some(whitespace),
        }
    }

    /// Returns all successive whitespace (and comments), if any, moving the cursor past it.
    pub fn skip_whitespace(&mut self) -> Option<&'a [u8]> {
        self.check_whitespace()
            .map(|whitespace| self.skip_n_unchecked(whitespace.len()))
    }

    fn maybe_skip_whitespace(&mut self) {
        if R::always_skip_whitespace() {
            self.skip_whitespace();
        }
    }

    fn check_unchecked_from(&self, from: usize, expected: &[u8]) -> Option<&'a [u8]> {
        let actual = &self.bytes()[from..(from + expected.len())];
        match actual == expected {
            true => Some(actual),
            false => None,
        }
    }

    fn check_from(&self, from: usize, expected: &[u8]) -> Option<&'a [u8]> {
        match from + expected.len() <= self.len() {
            true => self.check_unchecked_from(from, expected),
            false => None,
        }
    }

    /// Returns the expected sequence of bytes, if present, without moving the cursor.
    pub fn check(&self, expected: &[u8]) -> Option<&'a [u8]> {
        self.check_from(self.cursor(), expected)
    }

    /// Returns the expected sequence of bytes, if present, moving the cursor past it.
    pub fn skip(&mut self, expected: &[u8]) -> Option<&'a [u8]> {
        self.check(expected)
            .map(|found| self.skip_n_unchecked(found.len()))
    }

    /// Returns the expected sequence of bytes, if present, moving the cursor past it.
    ///
    /// # Errors
    /// Returns an error if the bytes are not found. Does not move the cursor in
    /// this case.
    pub fn expect(&mut self, expected: &[u8]) -> Result<&'a [u8]> {
        self.expect_not_finished()?;

        let start = self.cursor();
        self.skip(expected).ok_or_else(|| {
            let actual = &self.bytes()[start..std::cmp::min(self.len(), start + expected.len())];
            Error {
                byte: start,
                kind: Kind::UnexpectedString(
                    String::from_utf8_lossy(expected).into_owned(),
                    String::from_utf8_lossy(actual).into_owned(),
                ),
            }
        })
    }

    fn check_matching_from<F>(&self, pos: usize, f: F) -> &'a [u8]
    where
        F: Fn(u8) -> bool,
    {
        let mut cur = pos;

        while cur < self.len() && f(self.bytes()[cur]) {
            cur += 1;
        }

        &self.bytes()[pos..cur]
    }

    /// Returns the longest sequence of bytes that match the given predicate without moving the
    /// cursor.
    pub fn check_matching<F>(&self, f: F) -> &'a [u8]
    where
        F: Fn(u8) -> bool,
    {
        self.check_matching_from(self.cursor(), f)
    }

    /// Returns the longest sequence of bytes that match the given predicate, moving the
    /// cursor past them.
    pub fn skip_matching<F>(&mut self, f: F) -> &'a [u8]
    where
        F: Fn(u8) -> bool,
    {
        let result = self.check_matching(f);
        self.skip_n_unchecked(result.len());
        result
    }

    /// Returns the identifier at the cursor, if one exists, without moving the cursor.
    pub fn check_ident(&self) -> Option<&'a [u8]> {
        let candidate = self.check_matching(|ch| R::is_ident_byte(ch));
        match candidate.len() > 0 && R::is_ident_start_byte(candidate[0]) {
            true => Some(candidate),
            false => None,
        }
    }

    /// Returns the identifier at the cursor, if one exists, moving the cursor past it.
    pub fn skip_ident(&mut self) -> Option<&'a [u8]> {
        self.check_ident()
            .map(|ident| self.skip_n_unchecked(ident.len()))
    }

    /// Returns the identifier at the cursor, if one exists, moving the cursor past it.
    ///
    /// # Errors
    /// Returns an error if there is no valid identifier at the cursor. Does not move the cursor in
    /// this case.
    pub fn expect_ident(&mut self) -> Result<&'a [u8]> {
        self.expect_not_finished()?;

        let start = self.cursor();
        self.skip_ident().ok_or_else(|| Error {
            byte: start,
            kind: Kind::InvalidIdentifier(self.lookahead_for_error_message(start)),
        })
    }

    fn lookahead_for_error_message(&self, from: usize) -> String {
        let byte_range = match R::is_whitespace_byte(self.bytes()[from]) {
            true => &self.bytes()[from..(from + 1)],
            false => self.check_matching_from(from, |ch| !R::is_whitespace_byte(ch)),
        };

        String::from_utf8_lossy(byte_range).into_owned()
    }

    /// Returns the keyword at the cursor, if one exists, without moving the cursor.
    ///
    /// A keyword can be any sequence of bytes not followed by an identifier character.
    pub fn check_keyword(&mut self, keyword: &[u8]) -> Option<&'a [u8]> {
        self.check(keyword).filter(|keyword| {
            let end = self.cursor() + keyword.len();
            end == self.len() || !R::is_ident_byte(self.bytes()[end])
        })
    }

    /// Returns the keyword at the cursor, if one exists, moving the cursor past it.
    ///
    /// A keyword can be any sequence of bytes not followed by an identifier character.
    pub fn skip_keyword(&mut self, keyword: &[u8]) -> Option<&'a [u8]> {
        self.check_keyword(keyword)
            .map(|keyword| self.skip_n_unchecked(keyword.len()))
    }

    /// Returns the keyword at the cursor, if one exists, moving the cursor past it.
    ///
    /// A keyword can be any sequence of bytes not followed by an identifier character.
    ///
    /// # Errors
    /// Returns an error if there is no keyword at the cursor. Does not move the cursor in
    /// this case.
    pub fn expect_keyword(&mut self, keyword: &[u8]) -> Result<&'a [u8]> {
        self.expect_not_finished()?;

        let start = self.cursor();
        self.skip_keyword(keyword).ok_or_else(|| Error {
            byte: start,
            kind: Kind::UnexpectedString(
                String::from_utf8_lossy(keyword).into_owned(),
                self.lookahead_for_error_message(start),
            ),
        })
    }

    /// Skip all tokens within a pair of matching parentheses, given by the opening byte.
    ///
    /// This method assumes that the cursor is _beyond_ the opening byte.
    ///
    /// # Examples
    /// ```rust
    /// use sashimi::Parser;
    ///
    /// let source = "nested { 'ignores } quotes' } }<- end";
    /// let mut parser: Parser = Parser::new(source);
    ///
    /// assert_eq!(
    ///     parser.skip_inside(b'{').unwrap(),
    ///     b"nested { 'ignores } quotes' } ",
    /// );
    /// ```
    ///
    /// # Errors
    /// Returns an error if no matching bracket is found by the end of the input.
    pub fn skip_inside(&mut self, first_opener: u8) -> Result<&'a [u8]> {
        let start = self.cursor();
        let mut parser = self.clone();

        let mut open_stack = vec![first_opener];

        while !parser.finished() && !open_stack.is_empty() {
            let byte = parser.bytes()[parser.cursor()];
            let opener = *open_stack.last().unwrap();

            let closed_type = R::NESTABLE_PARENS
                .iter()
                .chain(R::NON_NESTABLE_PARENS.iter())
                .find(|pair| pair.1 == byte);
            let opener_type = R::NON_NESTABLE_PARENS.iter().find(|pair| pair.0 == byte);

            match (closed_type, opener_type) {
                (Some(c), _) if opener == c.0 => {
                    open_stack.pop();
                }
                (_, Some(o)) => {
                    open_stack.push(o.0);
                }
                _ if byte == first_opener => open_stack.push(byte),
                _ => (),
            }

            if !open_stack.is_empty() {
                parser.skip_n(1)?;
            }
        }

        if open_stack.is_empty() {
            *self = parser;
            Ok(&self.bytes()[start..self.cursor()])
        } else {
            Err(Error {
                byte: parser.cursor(),
                kind: Kind::UnexpectedEnd(self.len()),
            })
        }
    }

    /// See `Parser::skip_inside`. The same, but consumes the opening and closing parentheses as
    /// well.
    pub fn skip_around(&mut self, opener: u8) -> Result<&'a [u8]> {
        let start = self.cursor();
        let closer = R::NESTABLE_PARENS
            .iter()
            .chain(R::NON_NESTABLE_PARENS.iter())
            .find(|pair| pair.0 == opener)
            .unwrap()
            .1;

        self.expect(&[opener])?;
        self.skip_inside(opener)?;
        self.expect(&[closer])?;
        let end = self.cursor();

        Ok(&self.bytes()[start..end])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! testcase {
        ($name:ident, $source:literal, $fn:ident ( $($arg:expr),* ), $result:expr, $remainder:literal) => {
            #[test]
            fn $name() {
                let parser = &mut DefaultParser::new($source);
                let result = parser.$fn($($arg),*);
                let remainder = &parser.bytes()[parser.cursor()..];
                assert_eq!(result, $result);
                assert_eq!(remainder, $remainder.as_bytes());
            }
        }
    }

    macro_rules! testcase_ok {
        ($name:ident, $source:literal, $fn:ident ( $($arg:expr),* ), $result:expr, $remainder:literal) => {
            #[test]
            fn $name() {
                let parser = &mut DefaultParser::new($source);
                let result = parser.$fn($($arg),*).unwrap();
                let remainder = &parser.bytes()[parser.cursor()..];
                assert_eq!(result, $result.as_bytes());
                assert_eq!(remainder, $remainder.as_bytes());
            }
        }
    }

    macro_rules! testcase_err {
        ($name:ident, $source:literal, $fn:ident ( $($arg:expr),* ), $remainder:literal, $errormsg:literal) => {
            #[test]
            fn $name() {
                let parser = &mut DefaultParser::new($source);
                let result = parser.$fn($($arg),*).unwrap_err();
                let remainder = &parser.bytes()[parser.cursor()..];
                assert_eq!(remainder, $remainder.as_bytes());
                assert_eq!(result.to_string(), $errormsg);
            }
        }
    }

    testcase!(check_a, "a", check(b"a"), Some(b"a".as_ref()), "a");
    testcase!(check_b, "b", check(b"b"), Some(b"b".as_ref()), "b");
    testcase!(
        check_word,
        "word rest",
        check(b"word"),
        Some(b"word".as_ref()),
        "word rest"
    );
    testcase!(check_fail, "a", check(b"b"), None, "a");
    testcase!(check_eof, "", check(b"b"), None, "");

    testcase!(skip_a, "a", skip(b"a"), Some(b"a".as_ref()), "");
    testcase!(skip_b, "b", skip(b"b"), Some(b"b".as_ref()), "");
    testcase!(
        skip_word,
        "word rest",
        skip(b"word"),
        Some(b"word".as_ref()),
        "rest"
    );
    testcase!(
        skip_trims,
        "word  \nend",
        skip(b"word"),
        Some(b"word".as_ref()),
        "end"
    );
    testcase!(skip_fail, "a", skip(b"b"), None, "a");
    testcase!(skip_eof, "", skip(b"b"), None, "");

    testcase_ok!(expect_a, "a", expect(b"a"), "a", "");
    testcase_ok!(expect_b, "b", expect(b"b"), "b", "");
    testcase_ok!(expect_word, "word", expect(b"word"), "word", "");
    testcase_ok!(expect_trims, "word  \nend", expect(b"word"), "word", "end");

    testcase_ok!(expect_ident_ok, "_var123", expect_ident(), "_var123", "");
    testcase_err!(
        expect_ident_err,
        "123var_",
        expect_ident(),
        "123var_",
        "Error at byte position 0: Expected identifier but got `123var_` instead"
    );

    testcase_err!(
        expect_fail,
        "b",
        expect(b"a"),
        "b",
        "Error at byte position 0: Expected `a` but got `b` instead"
    );
    testcase_err!(
        expect_eof,
        "",
        expect(b"a"),
        "",
        "Error at byte position 0: Unexpected end of source, which is 0 bytes"
    );
    testcase_err!(
        expect_very_fail,
        "no is the answer we actually got",
        expect(b"yes"),
        "no is the answer we actually got",
        "Error at byte position 0: Expected `yes` but got `no ` instead"
    );

    testcase!(
        skip_spaces,
        "   hi",
        skip_whitespace(),
        Some(b"   ".as_ref()),
        "hi"
    );
    testcase!(
        skip_newlines,
        " \n \nhey",
        skip_whitespace(),
        Some(b" \n \n".as_ref()),
        "hey"
    );
    testcase!(
        skip_single_comments,
        "// ignore this\nYo",
        skip_whitespace(),
        Some(b"// ignore this\n".as_ref()),
        "Yo"
    );
    testcase!(
        skip_multi_comment,
        "/* ignore this */Greetings!",
        skip_whitespace(),
        Some(b"/* ignore this */".as_ref()),
        "Greetings!"
    );
    testcase!(
        skip_nested_multi_comment,
        "/* ignore /* this */ too */Greetings!",
        skip_whitespace(),
        Some(b"/* ignore /* this */ too */".as_ref()),
        "Greetings!"
    );

    testcase_ok!(skip_inside, "inside }", skip_inside(b'{'), "inside ", "}");
    testcase_ok!(
        skip_inside_unmatched,
        "inside ] }",
        skip_inside(b'{'),
        "inside ] ",
        "}"
    );
    testcase_ok!(
        skip_inside_ignore_string,
        "inside \"}\" }",
        skip_inside(b'{'),
        "inside \"}\" ",
        "}"
    );
    testcase_ok!(
        skip_inside_ignore_nested,
        " one { two { three } } } done",
        skip_inside(b'{'),
        " one { two { three } } ",
        "} done"
    );
    testcase_err!(
        skip_inside_early_end,
        "inside",
        skip_inside(b'{'),
        "inside",
        "Error at byte position 6: Unexpected end of source, which is 6 bytes"
    );
}
