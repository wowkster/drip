use std::{io, path::PathBuf, rc::Rc};

use colored::{Color, Colorize};
use lexer::{Lexer, TokenKind};

use self::lexer::Span;
use crate::{frontend::lexer::Keyword, index::simple_index};

pub mod ast;
pub mod intern;
pub mod lexer;
pub mod parser;

simple_index! {
    pub struct SourceFileId;
}

#[derive(Debug, Clone)]
pub struct SourceFile {
    pub contents: Box<str>,
    pub origin: SourceFileOrigin,
}

impl SourceFile {
    pub fn read_from_path(path: impl AsRef<std::path::Path>) -> Result<Self, io::Error> {
        let contents = std::fs::read_to_string(&path)?;

        Ok(Self {
            contents: contents.into(),
            origin: SourceFileOrigin::File(path.as_ref().into()),
        })
    }

    pub fn as_path(&self) -> &PathBuf {
        match &self.origin {
            SourceFileOrigin::File(path) => path,
            _ => panic!("source file is not a file: {:?}", self.origin),
        }
    }

    pub fn value_of_span(&self, span: Span) -> &str {
        if span == Span::INVALID {
            unreachable!("tried to get value invalid span");
        }

        &self.contents[span.start..span.end]
    }

    pub fn format_span_position(&self, span: Span) -> String {
        if span == Span::INVALID {
            unreachable!("tried to format invalid span");
        }

        format!(
            "{}:{}:{}",
            self.origin,
            self.row_for_position(span.start),
            self.column_for_position(span.start)
        )
    }

    pub fn row_for_position(&self, position: usize) -> usize {
        let mut row = 1;

        for c in self.contents.bytes().take(position) {
            if c == b'\n' {
                row += 1;
            }
        }

        row
    }

    pub fn column_for_position(&self, position: usize) -> usize {
        let mut col = 1;

        for c in self.contents.bytes().take(position) {
            if c == b'\n' {
                col = 0;
            }

            col += 1;
        }

        col
    }

    pub fn highlight_span(&self, span: Span) {
        if span == Span::INVALID {
            unreachable!("tried to highlight invalid span");
        }

        let lines: Vec<_> = self.contents.lines().collect();

        let span_starting_row = self.row_for_position(span.start);
        let span_ending_row = self.row_for_position(span.end);

        let span_starting_column = self.column_for_position(span.start);
        let span_ending_column = self.column_for_position(span.end);

        // Print the lines around and including the one with the error
        let start_idx = span_starting_row.saturating_sub(3);

        // Isolate the lines we care about
        let lines_to_highlight = &lines[start_idx..span_starting_row];

        // Print each line and the line number
        for (n, line) in lines_to_highlight.iter().enumerate() {
            // TODO: used cached tokenization based on the module id?
            // TODO: make sure to preserve tokens that span multiple lines like multi-line strings

            eprint!("{}", format!("{:>3}: ", n + start_idx + 1).white());

            let source = Self {
                contents: line.to_string().into(),
                origin: self.origin.clone(),
            };

            let mut lexer = Lexer::new(&source);

            let mut last_end = 0;
            let mut last_token_kind = None::<TokenKind>;

            while let Some(token) = lexer.next() {
                eprint!("{}", " ".repeat(token.span.start - last_end));
                last_end = token.span.end;

                let color = match token.kind {
                    TokenKind::Keyword(_) => Color::Magenta,
                    TokenKind::Identifier => {
                        if lexer.peek().is_some_and(|t| t.kind == TokenKind::OpenParen) {
                            Color::Blue
                        } else if last_token_kind.is_some_and(|kind| {
                            matches!(
                                kind,
                                TokenKind::Colon
                                    | TokenKind::Arrow
                                    | TokenKind::Keyword(Keyword::As)
                            )
                        }) {
                            // TODO: for more accurate output, we could cache
                            // the results of parsing to see what identifier
                            // tokens turned into types
                            Color::Yellow
                        } else {
                            Color::BrightWhite
                        }
                    }
                    TokenKind::BooleanLiteral
                    | TokenKind::ByteLiteral
                    | TokenKind::CharLiteral
                    | TokenKind::IntegerLiteral
                    | TokenKind::FloatLiteral => Color::BrightYellow,
                    TokenKind::StringLiteral
                    | TokenKind::ByteStringLiteral
                    | TokenKind::CStringLiteral => Color::Green,
                    TokenKind::OpenParen
                    | TokenKind::CloseParen
                    | TokenKind::OpenBracket
                    | TokenKind::CloseBracket
                    | TokenKind::OpenBrace
                    | TokenKind::CloseBrace
                    | TokenKind::Semicolon
                    | TokenKind::Comma
                    | TokenKind::Dot
                    | TokenKind::Colon
                    | TokenKind::DoubleColon
                    | TokenKind::Arrow
                    | TokenKind::Bang
                    | TokenKind::Tilde
                    | TokenKind::Asterisk
                    | TokenKind::Minus
                    | TokenKind::Ampersand
                    | TokenKind::Plus
                    | TokenKind::Divide
                    | TokenKind::Modulus
                    | TokenKind::LogicalAnd
                    | TokenKind::LogicalOr
                    | TokenKind::BitwiseXor
                    | TokenKind::BitwiseOr
                    | TokenKind::ShiftLeft
                    | TokenKind::ShiftRight
                    | TokenKind::DoubleEquals
                    | TokenKind::NotEquals
                    | TokenKind::LessThan
                    | TokenKind::LessThanOrEqualTo
                    | TokenKind::GreaterThan
                    | TokenKind::GreaterThanOrEqualTo
                    | TokenKind::Equals
                    | TokenKind::PlusEquals
                    | TokenKind::MinusEquals
                    | TokenKind::MultiplyEquals
                    | TokenKind::DivideEquals
                    | TokenKind::ModulusEquals
                    | TokenKind::LogicalAndEquals
                    | TokenKind::LogicalOrEquals
                    | TokenKind::BitwiseXorEquals
                    | TokenKind::BitwiseAndEquals
                    | TokenKind::BitwiseOrEquals
                    | TokenKind::ShiftLeftEquals
                    | TokenKind::ShiftRightEquals => Color::White,
                };

                eprint!("{}", source.value_of_span(token.span).color(color));

                last_token_kind = Some(token.kind)
            }

            eprintln!()
        }

        // TODO: better highlight multi-line spans

        let prepending_count = span_starting_column + 4;
        let token_width = if span_ending_row == span_starting_row {
            span_ending_column - span_starting_column
        } else {
            1
        };

        // Print the space before the highlight
        eprint!("{}", String::from(" ").repeat(prepending_count));

        // Print the underline highlight
        eprintln!(
            "{}",
            String::from("^")
                .repeat(if token_width > 0 { token_width } else { 1 })
                .red()
        );

        // Print the space before "here"
        eprint!("{}", String::from(" ").repeat(prepending_count));

        eprintln!("{}", "here".red());
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum SourceFileOrigin {
    Memory,
    File(PathBuf),
}

impl core::fmt::Display for SourceFileOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SourceFileOrigin::Memory => f.write_str("<memory>"),
            SourceFileOrigin::File(path) => f.write_fmt(format_args!("{}", path.display())),
        }
    }
}
