use crate::lexer::LexError;
use crate::parser::ast::{
    AstError, ErrorNode, ErrorNodeKind, ErrorRecovery, ParseError, UntypedExprKind,
};
use crate::span::Span;

///! A bridge from LALRPOP types to our own.

pub fn map_lalrpop_error(error: &ParseError) -> Span<AstError> {
    match error {
        &ParseError::UnrecognizedEOF { location, .. } => {
            (location..location, AstError::UnrecognizedEOF)
        }
        &ParseError::InvalidToken { location } => (
            location..location,
            AstError::LexError(LexError::InvalidToken),
        ),
        &ParseError::UnrecognizedToken {
            token,
            ref expected,
        } => (
            token.0..token.2,
            AstError::UnexpectedToken(token.1.to_string(), expected.clone()),
        ),
        &ParseError::ExtraToken { token } => {
            (token.0..token.2, AstError::LexError(LexError::InvalidToken))
        }
        ParseError::User { error } => (std::ops::Range::<usize>::from(error), error.item.clone()),
    }
    .into()
}

impl UntypedExprKind {
    /// Called by the lalrpop grammar to record recovery actions
    pub fn from_error(error_recovery: &ErrorRecovery<'_>) -> UntypedExprKind {
        UntypedExprKind::Error(ErrorNode {
            kind: ErrorNodeKind::ParseError(map_lalrpop_error(&error_recovery.error).item),
            expr: None,
        })
    }
}
