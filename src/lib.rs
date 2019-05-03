use failure::Fail;

#[derive(Debug, Fail)]
#[fail(display = "Error at byte position {}: `{}`", byte, kind)]
pub struct ParseError {
    pub byte: usize,
    pub kind: ParseErrorKind,
}

#[derive(Debug, Fail)]
pub enum ParseErrorKind {
    #[fail(display = "Unexpected end of file")]
    UnexpectedEOF,

    #[fail(display = "Unexpected byte")]
    UnexpectedByte,

    #[fail(display = "Missing closing byte")]
    NoClosingByte,
}

pub struct Parser<'a> {
    source: &'a [u8],
    cursor: usize,
}

impl<'a> Parser<'a> {
    pub fn new(source: &'a str) -> Self {
        Parser {
            source: source.as_bytes(),
            cursor: 0,
        }
    }

    fn is_whitespace(&self, ch: u8) -> bool {
        match ch {
            b' ' | b'\t' | b'\r' => true,
            _ => false,
        }
    }

    fn is_ident_char(&self, ch: u8) -> bool {
        ch == b'_'
            || (b'a' <= ch && ch <= b'z')
            || (b'A' <= ch && ch <= b'Z')
            || (b'0' <= ch && ch <= b'9')
    }

    fn is_ident_start(&self, ch: u8) -> bool {
        ch == b'_' || (b'a' <= ch && ch <= b'z') || (b'A' <= ch && ch <= b'Z')
    }

    #[inline(always)]
    pub fn source(&self) -> &'a str {
        unsafe { std::str::from_utf8_unchecked(self.source) }
    }

    #[inline(always)]
    pub fn cursor(&self) -> usize {
        self.cursor
    }

    #[inline(always)]
    pub fn finished(&self) -> bool {
        self.cursor == self.source.len()
    }

    pub fn skip_whitespace(&mut self) {
        let mut in_comment = false;
        loop {
            // TODO: Multi-line comments
            if self.skip_only(b"//") {
                in_comment = true;
            } else if self.skip_only(b"\n") {
                in_comment = false;
            } else {
                if self.finished() || !(in_comment || self.is_whitespace(self.source[self.cursor]))
                {
                    break;
                }

                self.cursor += 1;
            }
        }
    }

    #[inline(always)]
    pub fn check(&self, next: &[u8]) -> bool {
        let end = self.cursor + next.len();
        end <= self.source.len() && &self.source[self.cursor..end] == next
    }

    pub fn check_matching<F>(&self, f: F) -> Option<&'a [u8]>
    where
        F: Fn(u8) -> bool,
    {
        let mut cursor = self.cursor;
        while cursor < self.source.len() && f(self.source[cursor]) {
            cursor += 1;
        }
        let result = &self.source[self.cursor..cursor];
        if result.is_empty() {
            None
        } else {
            Some(result)
        }
    }

    pub fn check_ident(&self) -> Option<&'a [u8]> {
        self.check_matching(|ch| self.is_ident_char(ch))
            .filter(|ident| self.is_ident_start(ident[0]))
    }

    pub fn check_keyword(&mut self, keyword: &[u8]) -> bool {
        let end = self.cursor + keyword.len();
        self.check(keyword) && (end == self.source.len() || !self.is_ident_char(self.source[end]))
    }

    pub fn skip(&mut self, next: &[u8]) -> bool {
        let skipped = self.check(next);
        if skipped {
            self.cursor += next.len();
            self.skip_whitespace();
        }
        skipped
    }

    pub fn skip_matching<F>(&mut self, f: F) -> Option<&'a [u8]>
    where
        F: Fn(u8) -> bool,
    {
        let result = self.check_matching(f);
        if let Some(result) = result {
            self.cursor += result.len();
            self.skip_whitespace();
        }
        result
    }

    pub fn skip_ident(&mut self) -> Option<&'a [u8]> {
        let result = self.check_ident();
        if let Some(result) = result {
            self.cursor += result.len();
            self.skip_whitespace();
        }
        result
    }

    pub fn skip_only(&mut self, next: &[u8]) -> bool {
        let skipped = self.check(next);
        if skipped {
            self.cursor += next.len();
        }
        skipped
    }

    pub fn skip_keyword(&mut self, keyword: &[u8]) -> bool {
        let success = self.check_keyword(keyword);
        if success {
            self.cursor += keyword.len();
            self.skip_whitespace();
        }
        success
    }

    #[inline(always)]
    pub fn expect(&mut self, next: &[u8]) -> Result<(), ParseError> {
        self.expect_with_fn(|parser| parser.skip(next))
    }

    #[inline(always)]
    pub fn expect_ident(&mut self) -> Result<&'a [u8], ParseError> {
        // TODO: Duplication
        if self.finished() {
            return Err(ParseError { byte: self.cursor, kind: ParseErrorKind::UnexpectedEOF });
        }

        self.skip_ident().ok_or_else(|| ParseError { byte: self.cursor, kind: ParseErrorKind::UnexpectedByte })
    }

    #[inline(always)]
    pub fn expect_only(&mut self, next: &[u8]) -> Result<(), ParseError> {
        self.expect_with_fn(|parser| parser.skip_only(next))
    }

    #[inline(always)]
    pub fn expect_keyword(&mut self, keyword: &[u8]) -> Result<(), ParseError> {
        self.expect_with_fn(|parser| parser.skip_keyword(keyword))
    }

    fn expect_with_fn<F>(&mut self, f: F) -> Result<(), ParseError>
    where
        F: Fn(&mut Self) -> bool,
    {
        if self.finished() {
            return Err(ParseError { byte: self.cursor, kind: ParseErrorKind::UnexpectedEOF });
        }

        if !f(self) {
            Err(ParseError { byte: self.cursor, kind: ParseErrorKind::UnexpectedByte })
        } else {
            Ok(())
        }
    }

    pub fn skip_around(&mut self, opener: u8, closer: u8) -> Result<(), ParseError> {
        self.expect(&[opener])?;
        self.skip_inside(opener, closer)?;
        self.expect(&[closer])?;
        Ok(())
    }

    pub fn skip_inside(&mut self, opener: u8, closer: u8) -> Result<(), ParseError> {
        let mut nesting = 1;
        loop {
            if self.check(&[opener]) {
                nesting += 1;
            } else if self.check(&[closer]) {
                nesting -= 1;
            }
            if nesting == 0 || self.finished() {
                break;
            }
            self.cursor += 1;
        }

        match nesting {
            0 => Ok(()),
            _ => Err(ParseError { byte: self.cursor, kind: ParseErrorKind::NoClosingByte }),
        }
    }

    pub fn scan_to(&mut self, byte: u8) -> &'a [u8] {
        let mut cursor = self.cursor;
        while cursor < self.source.len() && self.source[cursor] != byte {
            cursor += 1;
        }
        let result = &self.source[self.cursor..cursor];
        self.cursor = cursor;
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! testcase {
        ($name:ident, $source:literal, $fn:ident ( $($arg:expr),* ), $result:expr, $remainder:literal) => {
            #[test]
            fn $name() {
                let parser = &mut Parser::new($source);
                let result = parser.$fn($($arg),*);
                let remainder = parser.source()[parser.cursor()..].as_bytes();
                assert_eq!(result, $result);
                assert_eq!(remainder, $remainder.as_bytes());
            }
        }
    }

    macro_rules! testcase_ok {
        ($name:ident, $source:literal, $fn:ident ( $($arg:expr),* ), $result:expr, $remainder:literal) => {
            #[test]
            fn $name() {
                let parser = &mut Parser::new($source);
                let result = parser.$fn($($arg),*).unwrap();
                let remainder = parser.source()[parser.cursor()..].as_bytes();
                assert_eq!(result, $result);
                assert_eq!(remainder, $remainder.as_bytes());
            }
        }
    }

    macro_rules! testcase_err {
        ($name:ident, $source:literal, $fn:ident ( $($arg:expr),* ), $remainder:literal) => {
            #[test]
            fn $name() {
                let parser = &mut Parser::new($source);
                let result = parser.$fn($($arg),*).iter().next().is_some();
                let remainder = parser.source()[parser.cursor()..].as_bytes();
                assert!(!result);
                assert_eq!(remainder, $remainder.as_bytes());
            }
        }
    }

    testcase!(check_a, "a", check(b"a"), true, "a");
    testcase!(check_b, "b", check(b"b"), true, "b");
    testcase!(check_word, "word", check(b"word"), true, "word");
    testcase!(check_fail, "b", check(b"a"), false, "b");
    testcase!(check_eof, "", check(b"a"), false, "");
    testcase!(skip_a, "a", skip(b"a"), true, "");
    testcase!(skip_b, "b", skip(b"b"), true, "");
    testcase!(skip_word, "word", skip(b"word"), true, "");
    testcase!(skip_trims, "word  \nend", skip(b"word"), true, "end");
    testcase!(skip_fail, "b", skip(b"a"), false, "b");
    testcase!(skip_eof, "", skip(b"a"), false, "");
    testcase_ok!(expect_a, "a", expect(b"a"), (), "");
    testcase_ok!(expect_b, "b", expect(b"b"), (), "");
    testcase_ok!(expect_word, "word", expect(b"word"), (), "");
    testcase_ok!(expect_trims, "word  \nend", expect(b"word"), (), "end");
    testcase_err!(expect_fail, "b", expect(b"a"), "b");
    testcase_err!(expect_eof, "", expect(b"a"), "");

    testcase!(
        check_ident,
        "abc",
        check_ident(),
        Some(b"abc".as_ref()),
        "abc"
    );
    testcase!(check_ident_eof, "", check_ident(), None, "");
}
