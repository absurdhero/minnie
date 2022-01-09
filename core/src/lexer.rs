use logos::Lexer as LogosLexer;
use logos::Logos;
use std::fmt::{Display, Formatter};
use thiserror::Error;

///! A custom lexer using the Logos library
///!
///! Inspired by the LALRPOP Logos integration example
///! at https://github.com/segeljakt/logos-lalrpop

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
    #[token("let")]
    Let,
    #[token("if")]
    If,
    #[token("else")]
    Else,
    #[regex("[a-z][a-zA-Z0-9_]*", |lex| lex.slice())]
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

    // token that represents lex errors
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

            // this is an unsatisfying string representation
            Token::Error => "<unhandled>",
            Token::Unexpected(s) => s,
        };
        write!(f, "{}", repr)
    }
}

#[derive(Clone, Error, Debug, PartialEq, Eq)]
pub enum LexError {
    #[error("invalid token")]
    InvalidToken((usize, usize)),
}

pub struct Lexer<'i> {
    logos: LogosLexer<'i, Token<'i>>,
    pub errors: Vec<LexError>,
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
    /// Convert error tokens to LexErrors
    fn convert(&mut self, token: Token<'i>) -> Result<Token<'i>, LexError> {
        let range = self.logos.span();
        match token {
            Token::Error => Err(LexError::InvalidToken((range.start, range.end))),
            t => Ok(t),
        }
    }
}
