use std::ops::Range;
use crate::lexer;
use crate::lexer::{Lexer, Token};
use thiserror::Error;
use crate::ast;

#[derive(Debug, Error)]
pub enum Error<'a> {
    #[error("{0:?}")]
    ParseError(ParseError<'a>),
    #[error("reached end of expression with an unterminated '{0}'")]
    UnterminatedDelimiter(char),
    #[error("unexpected end of expression")]
    UnexpectedEOF,
}

#[derive(Debug, Error)]
#[error("{msg}")]
pub struct ParseError<'a> {
    msg: String,
    span: &'a str,
    location: Range<usize>,
}

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    input: &'a str,
    next: Option<<lexer::Lexer<'a> as Iterator>::Item>,
}

impl Parser<'_> {
    pub fn new(program: &str) -> Parser {
        Parser { lexer: Lexer::new(program), input: program, next: None }
    }

    pub fn parse(&mut self) -> Result<ast::Expr, Error> {
        self.next();
        match self.expr() {
            Some(e) => e,
            None => Err(Error::UnexpectedEOF),
        }
    }

    fn next(&mut self) {
        self.next = self.lexer.next();
    }

    fn parse_error(&self, msg: &str, span: &Range<usize>) -> Option<Result<ast::Expr, Error>> {
        Some(Err(Error::ParseError(ParseError { msg: msg.to_string(), span: &self.input[span.clone()], location: span.clone() })))
    }

    fn expr(&mut self) -> Option<Result<ast::Expr, Error>> {
        self.lexer.next();
        None
    }

    fn term(&mut self) -> Option<Result<ast::Expr, Error>> {
        match self.next {
            None => None,
            Some((Token::ParenStart, ref token_span)) => {
                self.next();
                let expr = self.expr();
                match expr {
                    Some(Ok(e)) => {
                        self.next();
                        match self.next {
                            Some((Token::ParenEnd, _)) => Some(Ok(e)),
                            _ => Some(Err(Error::UnterminatedDelimiter('('))),
                        }
                    },
                    Some(Err(e)) => Some(Err(e)),
                    None => self.parse_error( "empty parens", token_span)
                }
            }
            Some((_, ref span)) => self.parse_error("unexpected token", span)
        }
    }
}
