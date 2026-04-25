use std::{
    collections::{BTreeMap, VecDeque},
    panic::Location,
    str::Chars,
};

use itertools::{PeekNth, peek_nth};
use once_cell::sync::Lazy;
use strum::EnumString;

use crate::SourceFile;

#[derive(Debug)]
pub struct Lexer<'source> {
    source: &'source SourceFile,
    position: usize,
    line_number: usize,
    chars: PeekNth<Chars<'source>>,
    peek_buffer: VecDeque<Token>,
}

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    /* Words */
    Keyword(Keyword), // fn
    Identifier,       // main

    /* Literals */
    BooleanLiteral,    // true
    ByteLiteral,       // b'A'
    CharLiteral,       // 'A'
    IntegerLiteral,    // 1
    FloatLiteral,      // 1.0
    StringLiteral,     // "hello, world"
    ByteStringLiteral, // b"hello, world"
    CStringLiteral,    // c"hello, world"

    /* Delimiters */
    OpenParen,    // (
    CloseParen,   // )
    OpenBracket,  // [
    CloseBracket, // ]
    OpenBrace,    // {
    CloseBrace,   // }
    Semicolon,    // ;
    Comma,        // ,

    /* Other */
    Dot,         // .
    Colon,       // :
    DoubleColon, // ::
    Arrow,       // ->

    /* Unary Ops */
    Bang,  // !
    Tilde, // ~

    /* Unary + Binary Ops */
    Asterisk,  // *
    Minus,     // -
    Ampersand, // &

    /* Binary Ops */
    Plus,                 // +
    Divide,               // /
    Modulus,              // %
    LogicalAnd,           // &&
    LogicalOr,            // ||
    BitwiseXor,           // ^
    BitwiseOr,            // |
    ShiftLeft,            // <<
    ShiftRight,           // >>
    DoubleEquals,         // ==
    NotEquals,            // !=
    LessThan,             // <
    LessThanOrEqualTo,    // <=
    GreaterThan,          // >
    GreaterThanOrEqualTo, // >=

    /* Assignment */
    Equals,           // =
    PlusEquals,       // +=
    MinusEquals,      // -=
    MultiplyEquals,   // *=
    DivideEquals,     // /=
    ModulusEquals,    // %=
    LogicalAndEquals, // &&=
    LogicalOrEquals,  // ||=
    BitwiseXorEquals, // ^=
    BitwiseAndEquals, // &=
    BitwiseOrEquals,  // |=
    ShiftLeftEquals,  // <<=
    ShiftRightEquals, // >>=
}

impl TokenKind {
    pub fn is_assignment_operator(&self) -> bool {
        matches!(
            self,
            Self::Equals
                | Self::PlusEquals
                | Self::MinusEquals
                | Self::MultiplyEquals
                | Self::DivideEquals
                | Self::ModulusEquals
                | Self::LogicalAndEquals
                | Self::LogicalOrEquals
                | Self::BitwiseXorEquals
                | Self::BitwiseAndEquals
                | Self::BitwiseOrEquals
                | Self::ShiftLeftEquals
                | Self::ShiftRightEquals
        )
    }

    pub fn is_comparison_operator(&self) -> bool {
        matches!(
            self,
            Self::NotEquals
                | Self::DoubleEquals
                | Self::LessThan
                | Self::LessThanOrEqualTo
                | Self::GreaterThan
                | Self::GreaterThanOrEqualTo
        )
    }

    pub fn is_bit_shift_operator(&self) -> bool {
        matches!(self, Self::ShiftLeft | Self::ShiftRight)
    }

    pub fn is_term_operator(&self) -> bool {
        matches!(self, Self::Plus | Self::Minus)
    }

    pub fn is_factor_operator(&self) -> bool {
        matches!(self, Self::Asterisk | Self::Divide | Self::Modulus)
    }

    pub fn is_unary_operator(&self) -> bool {
        matches!(
            self,
            Self::Asterisk | Self::Bang | Self::Tilde | Self::Minus | Self::Ampersand
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, EnumString)]
#[strum(serialize_all = "snake_case")]
pub enum Keyword {
    Fn,
    Let,
    Mut,
    If,
    Else,
    While,
    As,
    Break,
    Continue,
    Return,
    Struct,
    Type,
    Static,
    #[strum(serialize = "self")]
    This,
    Enum,
    Mod,
}

/// Table of single char tokens (matched after longer sequences are checked for)
static SINGLE_TOKENS: Lazy<BTreeMap<char, TokenKind>> = Lazy::new(|| {
    BTreeMap::from([
        ('(', TokenKind::OpenParen),
        (')', TokenKind::CloseParen),
        ('[', TokenKind::OpenBracket),
        (']', TokenKind::CloseBracket),
        ('{', TokenKind::OpenBrace),
        ('}', TokenKind::CloseBrace),
        (';', TokenKind::Semicolon),
        (',', TokenKind::Comma),
        ('!', TokenKind::Bang),
        ('~', TokenKind::Tilde),
        ('.', TokenKind::Dot),
        (':', TokenKind::Colon),
        ('*', TokenKind::Asterisk),
        ('-', TokenKind::Minus),
        ('=', TokenKind::Equals),
        ('+', TokenKind::Plus),
        ('/', TokenKind::Divide),
        ('%', TokenKind::Modulus),
        ('^', TokenKind::BitwiseXor),
        ('&', TokenKind::Ampersand),
        ('|', TokenKind::BitwiseOr),
        ('<', TokenKind::LessThan),
        ('>', TokenKind::GreaterThan),
    ])
});

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub const INVALID: Self = Self {
        start: usize::MAX,
        end: usize::MAX,
    };

    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn merge(first: Self, second: Self) -> Self {
        assert!(first.start <= second.start);
        assert!(first.start <= second.end);
        assert!(first.end <= second.end);

        Self::new(first.start, second.end)
    }
}

impl<'source> Lexer<'source> {
    pub fn new(source: &'source SourceFile) -> Self {
        Self {
            source,
            chars: peek_nth(source.contents.chars()),
            position: 0,
            line_number: 0,
            peek_buffer: VecDeque::new(),
        }
    }

    pub fn is_eof(&self) -> bool {
        self.position >= self.source.contents.len()
    }

    pub fn source(&self) -> &SourceFile {
        self.source
    }

    pub fn line_number(&self) -> usize {
        self.line_number
    }

    pub fn column(&self) -> usize {
        let mut pos = 0;

        for line in self
            .source
            .contents
            .split_inclusive('\n')
            .take(self.line_number)
        {
            pos += line.len()
        }

        self.position - pos
    }

    #[track_caller]
    fn consume_char(&mut self) -> char {
        let c = self.chars.next().unwrap();
        self.position += c.len_utf8();
        c
    }

    #[track_caller]
    fn report_fatal_error(&self, message: &str) -> ! {
        #[cfg(feature = "error-backtrace")]
        eprintln!("error backtrace: {}", Location::caller());

        eprintln!(
            "Fatal error reported in Lexer (at {}:{}:{}:",
            self.source.origin,
            self.line_number + 1,
            self.column() + 1
        );
        eprintln!("{message}");
        std::process::exit(1);
    }

    fn ignore_whitespace(&mut self) {
        while let Some(c) = self.chars.peek().copied() {
            if !c.is_ascii_whitespace() {
                break;
            }

            if c == '\n' {
                self.line_number += 1;
            }

            self.consume_char();
        }
    }

    fn ignore_line(&mut self) {
        while let Some(c) = self.chars.peek().copied() {
            if c == '\n' {
                break;
            }

            self.consume_char();
        }
    }

    fn read_wrapped_escapable(&mut self, wrapper: char, kind: TokenKind) -> Token {
        let start_position = self.position;

        // Consume first wrapper
        self.consume_char();

        while let Some(c) = self.chars.peek().copied() {
            if c == '\n' {
                self.report_fatal_error(&format!(
                    "Reached end of line while reading wrapped literal: {kind:?}",
                ));
            }

            // Consume chars within the wrapped literal
            self.consume_char();

            // If we encountered an escape sequence, keep going
            if c == '\\' && self.chars.peek().is_some_and(|c| *c == wrapper) {
                self.consume_char();
            }

            if c == wrapper {
                return Token {
                    span: self.new_span(start_position),
                    kind,
                };
            }
        }

        self.report_fatal_error(&format!(
            "Reached end of file while reading wrapped literal: {kind:?}",
        ))
    }

    fn read_prefixed_wrapped_escapable(
        &mut self,
        prefix: char,
        wrapper: char,
        kind: TokenKind,
    ) -> Token {
        let start_position = self.position;

        assert_eq!(self.consume_char(), prefix);

        self.read_wrapped_escapable(wrapper, kind);

        Token {
            span: self.new_span(start_position),
            kind,
        }
    }

    // Keyword, identifier, or boolean literal
    fn read_word(&mut self) -> Token {
        let start_position = self.position;

        while let Some(c) = self.chars.peek().copied() {
            if !(c.is_ascii_alphanumeric() || c == '_') {
                break;
            }

            self.consume_char();
        }

        let span = self.new_span(start_position);
        let value = self.source.value_of_span(span);

        let kind = if let Ok(keyword) = value.parse() {
            TokenKind::Keyword(keyword)
        } else {
            match value {
                "true" | "false" => TokenKind::BooleanLiteral,
                _ => TokenKind::Identifier,
            }
        };

        Token { kind, span }
    }

    fn read_number(&mut self) -> Token {
        let start_position = self.position;
        let mut kind = TokenKind::IntegerLiteral;

        assert!(self.chars.peek().is_some());

        while let Some(c) = self.chars.peek().copied() {
            if c == '.' {
                kind = TokenKind::FloatLiteral;
                self.read_decimal_part();
                break;
            }

            if !c.is_ascii_digit() {
                break;
            }

            self.consume_char();
        }

        Token {
            kind,
            span: self.new_span(start_position),
        }
    }

    fn read_decimal_part(&mut self) -> Token {
        let start_position = self.position;

        self.consume_char();

        while let Some(c) = self.chars.peek().copied() {
            if !c.is_ascii_digit() {
                break;
            }

            self.consume_char();
        }

        Token {
            kind: TokenKind::FloatLiteral,
            span: self.new_span(start_position),
        }
    }

    fn read_single(&mut self, kind: TokenKind) -> Token {
        let start_position = self.position;

        self.consume_char();

        Token {
            kind,
            span: self.new_span(start_position),
        }
    }

    fn read_double(&mut self, kind: TokenKind) -> Token {
        let start_position = self.position;

        self.consume_char();
        self.consume_char();

        Token {
            kind,
            span: self.new_span(start_position),
        }
    }

    fn read_triple(&mut self, kind: TokenKind) -> Token {
        let start_position = self.position;

        self.consume_char();
        self.consume_char();
        self.consume_char();

        Token {
            kind,
            span: self.new_span(start_position),
        }
    }

    fn new_span(&self, start: usize) -> Span {
        Span {
            start,
            end: self.position,
        }
    }

    pub fn peek(&mut self) -> Option<Token> {
        if !self.peek_buffer.is_empty() {
            return self.peek_buffer.front().cloned();
        }

        if let Some(token) = self.next() {
            self.peek_buffer.push_back(token);
        }

        self.peek_buffer.front().cloned()
    }

    pub fn peek_nth(&mut self, n: usize) -> Option<Token> {
        if self.peek_buffer.len() > n {
            return self.peek_buffer.get(n).cloned();
        }

        let mut peek_buffer = core::mem::take(&mut self.peek_buffer);

        let delta = n - self.peek_buffer.len() + 1;

        for _ in 0..delta {
            if let Some(token) = self.next() {
                peek_buffer.push_back(token);
            } else {
                break;
            }
        }

        self.peek_buffer = peek_buffer;
        self.peek_buffer.get(n).cloned()
    }

    pub fn next(&mut self) -> Option<Token> {
        if !self.peek_buffer.is_empty() {
            return self.peek_buffer.pop_front();
        }

        while let Some(c) = self.chars.peek().copied() {
            if !c.is_ascii() {
                self.report_fatal_error(&format!("Unexpected non-ascii character in stream: `{c}`"))
            }

            let token = match c {
                // Ignore whitespace
                c if c.is_whitespace() => {
                    self.ignore_whitespace();
                    continue;
                }
                // Ignore comments
                '/' if self.chars.peek_nth(1).is_some_and(|c| *c == '/') => {
                    self.ignore_line();
                    continue;
                }

                // Byte string literals
                'b' if self.chars.peek_nth(1).is_some_and(|c| *c == '"') => {
                    self.read_prefixed_wrapped_escapable('b', '"', TokenKind::ByteStringLiteral)
                }
                // Byte literals
                'b' if self.chars.peek_nth(1).is_some_and(|c| *c == '\'') => {
                    self.read_prefixed_wrapped_escapable('b', '\'', TokenKind::ByteLiteral)
                }
                // C string literals
                'c' if self.chars.peek_nth(1).is_some_and(|c| *c == '"') => {
                    self.read_prefixed_wrapped_escapable('c', '"', TokenKind::CStringLiteral)
                }
                // String literals
                '"' => self.read_wrapped_escapable('"', TokenKind::StringLiteral),
                // Char literals
                '\'' => self.read_wrapped_escapable('\'', TokenKind::CharLiteral),

                // Integer and float literals
                n if n.is_ascii_digit() => self.read_number(),
                '.' if self.chars.peek_nth(1).is_some_and(|c| c.is_ascii_digit()) => {
                    self.read_decimal_part()
                }

                // Identifiers, keywords, and boolean literals
                a if a.is_ascii_alphabetic() || a == '_' => self.read_word(),

                // Arrow (->)
                '-' if self.chars.peek_nth(1).is_some_and(|c| *c == '>') => {
                    self.read_double(TokenKind::Arrow)
                }
                // Double colon (::)
                ':' if self.chars.peek_nth(1).is_some_and(|c| *c == ':') => {
                    self.read_double(TokenKind::DoubleColon)
                }

                // Double Equals (==)
                '=' if self.chars.peek_nth(1).is_some_and(|c| *c == '=') => {
                    self.read_double(TokenKind::DoubleEquals)
                }
                // Not Equals (!=)
                '!' if self.chars.peek_nth(1).is_some_and(|c| *c == '=') => {
                    self.read_double(TokenKind::NotEquals)
                }
                // Less than or equal (<=)
                '<' if self.chars.peek_nth(1).is_some_and(|c| *c == '=') => {
                    self.read_double(TokenKind::LessThanOrEqualTo)
                }
                // Greater than or equal (>=)
                '>' if self.chars.peek_nth(1).is_some_and(|c| *c == '=') => {
                    self.read_double(TokenKind::GreaterThanOrEqualTo)
                }

                // Plus equals (+=)
                '+' if self.chars.peek_nth(1).is_some_and(|c| *c == '=') => {
                    self.read_double(TokenKind::PlusEquals)
                }
                // Minus equals (-=)
                '-' if self.chars.peek_nth(1).is_some_and(|c| *c == '=') => {
                    self.read_double(TokenKind::MinusEquals)
                }
                // Multiply equals (*=)
                '*' if self.chars.peek_nth(1).is_some_and(|c| *c == '=') => {
                    self.read_double(TokenKind::MultiplyEquals)
                }
                // Divide equals (/=)
                '/' if self.chars.peek_nth(1).is_some_and(|c| *c == '=') => {
                    self.read_double(TokenKind::DivideEquals)
                }
                // Modulus equals (%=)
                '%' if self.chars.peek_nth(1).is_some_and(|c| *c == '=') => {
                    self.read_double(TokenKind::ModulusEquals)
                }
                // Bitwise and equals (&=)
                '&' if self.chars.peek_nth(1).is_some_and(|c| *c == '=') => {
                    self.read_double(TokenKind::BitwiseAndEquals)
                }
                // Bitwise or equals (|=)
                '|' if self.chars.peek_nth(1).is_some_and(|c| *c == '=') => {
                    self.read_double(TokenKind::BitwiseOrEquals)
                }
                // Bitwise xor equals (^=)
                '^' if self.chars.peek_nth(1).is_some_and(|c| *c == '=') => {
                    self.read_double(TokenKind::BitwiseXorEquals)
                }

                // Shift left equals (<<=)
                '<' if self.chars.peek_nth(1).is_some_and(|c| *c == '<')
                    && self.chars.peek_nth(2).is_some_and(|c| *c == '=') =>
                {
                    self.read_triple(TokenKind::ShiftLeftEquals)
                }
                // Shift right equals (>>=)
                '>' if self.chars.peek_nth(1).is_some_and(|c| *c == '>')
                    && self.chars.peek_nth(2).is_some_and(|c| *c == '=') =>
                {
                    self.read_triple(TokenKind::ShiftRightEquals)
                }
                // Shift left (<<)
                '<' if self.chars.peek_nth(1).is_some_and(|c| *c == '<') => {
                    self.read_double(TokenKind::ShiftLeft)
                }
                // Shift right (>>)
                '>' if self.chars.peek_nth(1).is_some_and(|c| *c == '>') => {
                    self.read_double(TokenKind::ShiftRight)
                }

                // Logical and equals (&&=)
                '&' if self.chars.peek_nth(1).is_some_and(|c| *c == '&')
                    && self.chars.peek_nth(2).is_some_and(|c| *c == '=') =>
                {
                    self.read_triple(TokenKind::LogicalAndEquals)
                }
                // Logical or equals (||=)
                '|' if self.chars.peek_nth(1).is_some_and(|c| *c == '|')
                    && self.chars.peek_nth(2).is_some_and(|c| *c == '=') =>
                {
                    self.read_triple(TokenKind::LogicalOrEquals)
                }
                // Logical And (&&)
                '&' if self.chars.peek_nth(1).is_some_and(|c| *c == '&') => {
                    self.read_double(TokenKind::LogicalAnd)
                }
                // Logical Or (||)
                '|' if self.chars.peek_nth(1).is_some_and(|c| *c == '|') => {
                    self.read_double(TokenKind::LogicalOr)
                }

                s if SINGLE_TOKENS.contains_key(&s) => {
                    self.read_single(*SINGLE_TOKENS.get(&s).unwrap())
                }
                c => self.report_fatal_error(&format!("Unexpected character in stream: `{c}`")),
            };

            return Some(token);
        }

        None
    }
}
