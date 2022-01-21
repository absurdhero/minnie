use crate::span::Span;
use logos::Lexer as LogosLexer;
use logos::Logos;
use std::fmt::{Display, Formatter};
use thiserror::Error;

#[cfg(feature = "serialize_ast")]
use serde::Serialize;

///! A custom lexer using the Logos library
///!
///! Inspired by the LALRPOP Logos integration example
///! at <https://github.com/segeljakt/logos-lalrpop>

/// Tokens
///
/// The Logos tokenizer matches most-specific patterns first
/// and it supports a subset of regex without greedy matching.
///
/// When adding new tokens, refer to <https://github.com/maciejhirsz/logos/issues/133>
/// to find working regular expressions for common language constructs.
#[derive(Logos, Copy, Clone, Debug, PartialEq)]
pub enum Token<'input> {
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[regex(r"([0-9]+)", |lex| lex.slice())]
    Num(&'input str),
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Multiply,
    #[token("/")]
    Divide,
    #[token("=")]
    Eq,
    #[token("==")]
    BoolEq,
    #[token("!=")]
    BoolNotEq,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token("<=")]
    LtEq,
    #[token(">=")]
    GtEq,
    #[token("let")]
    Let,
    #[token("if")]
    If,
    #[token("else")]
    Else,
    #[regex("(\\p{XID_Start}|_)\\p{XID_Continue}*", |lex| lex.slice())]
    ID(&'input str),
    #[token(",")]
    Comma,
    #[token("{")]
    CurlyStart,
    #[token("}")]
    CurlyEnd,
    #[token("(")]
    ParenStart,
    #[token(")")]
    ParenEnd,
    #[token(";")]
    Semi,

    // types
    #[token(":")]
    Colon,
    #[token("int")]
    Int,
    #[token("bool")]
    Bool,

    // functions
    #[token("fn")]
    Fn,
    #[token("->")]
    RArrow,
    #[token("pub")]
    Pub,

    /// token that represents lex errors
    #[error]
    // skip whitespace
    #[regex(r"[ \t\n\f]+", logos::skip)]
    // skip // comments
    #[regex(r"//[^\r\n]*", logos::skip)]
    Error,

    // used to fabricate error tokens with a string for debugging
    Unexpected(&'input str),
}

impl<'i> Display for Token<'i> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let repr = match self {
            Token::True => "true",
            Token::False => "false",
            Token::Num(s) => s,
            Token::Plus => "+",
            Token::Minus => "-",
            Token::Multiply => "*",
            Token::Divide => "/",
            Token::BoolEq => "==",
            Token::BoolNotEq => "!=",
            Token::Lt => "<",
            Token::Gt => ">",
            Token::LtEq => "<=",
            Token::GtEq => ">=",
            Token::Eq => "=",
            Token::Let => "let",
            Token::If => "if",
            Token::Else => "else",
            Token::ID(s) => s,
            Token::Comma => ",",
            Token::CurlyStart => "{",
            Token::CurlyEnd => "}",
            Token::ParenStart => "(",
            Token::ParenEnd => ")",
            Token::Semi => ";",

            Token::Colon => ":",
            Token::Int => "int",
            Token::Bool => "bool",

            Token::Fn => "fn",
            Token::RArrow => "->",
            Token::Pub => "pub",

            // this is an unsatisfying string representation
            Token::Error => "<unhandled>",
            Token::Unexpected(s) => s,
        };
        write!(f, "{}", repr)
    }
}

#[derive(Clone, Error, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize_ast", derive(Serialize))]
pub enum LexError {
    #[error("invalid token")]
    InvalidToken,
}

pub struct Lexer<'i> {
    logos: LogosLexer<'i, Token<'i>>,
    pub errors: Vec<Span<LexError>>,
}

impl<'i> Iterator for Lexer<'i> {
    type Item = (usize, Token<'i>, usize);
    fn next(&mut self) -> Option<Self::Item> {
        let token = loop {
            let token = self.logos.next()?;
            match self.convert(token) {
                Ok(token) => break token,
                Err(err) => self.errors.push(err),
            }
        };
        let span = self.logos.span();
        Some((span.start, token, span.end))
    }
}

impl<'i> Lexer<'i> {
    pub fn new(input: &'i str) -> Self {
        Self {
            errors: Vec::new(),
            logos: LogosLexer::new(input),
        }
    }
    /// Convert error tokens to `LexError`
    fn convert(&mut self, token: Token<'i>) -> Result<Token<'i>, Span<LexError>> {
        let range = self.logos.span();
        match token {
            Token::Error => Err((range.start, LexError::InvalidToken, range.end).into()),
            t => Ok(t),
        }
    }
}
