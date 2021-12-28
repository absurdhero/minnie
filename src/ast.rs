use crate::grammar;
use crate::lexer::{LexError, Lexer, Token};
use crate::span::Span;
use thiserror::Error;

pub type ParseError<'input> = lalrpop_util::ParseError<usize, Token<'input>, Span<AstError>>;
pub type ErrorRecovery<'input> = lalrpop_util::ErrorRecovery<usize, Token<'input>, Span<AstError>>;

pub type SpExpr = Span<Box<Expr>>;

impl PartialEq for SpExpr {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.ty == other.ty
    }
}
impl Eq for SpExpr {}

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum AstError {
    #[error("{msg}")]
    Error { msg: String },
    #[error("expected {expected:?} but found {found:?}")]
    TypeError { expected: Type, found: Type },
    #[error("unknown type")]
    UnknownTypeError,
    // Not used. LexError are converted directly into ParseError
    #[error(transparent)]
    LexError(#[from] LexError),
}

#[derive(Debug, PartialEq, Eq)]
pub enum ExprKind {
    Error(Option<Type>),
    Number(String),
    Bool(bool),
    Negate(SpExpr),
    Op(SpExpr, Opcode, SpExpr),
    If(SpExpr, SpExpr, SpExpr),
    Sequence(Vec<SpExpr>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Opcode {
    Mul,
    Div,
    Add,
    Sub,
}

/// Types supported by the language
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    Int64,
    Bool,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Type,
}

impl Expr {
    pub fn new(expr: ExprKind) -> Result<Box<Expr>, AstError> {
        expr.into_expr().map(Box::new)
    }
}

impl<'a> ExprKind {
    pub fn into_expr(self) -> Result<Expr, AstError> {
        let ty = self.infer_type()?;
        Ok(Expr { kind: self, ty })
    }

    pub fn infer_type(&self) -> Result<Type, AstError> {
        match self {
            // help the type checker recover from errors by letting the parser guess a type
            ExprKind::Error(Some(t)) => Ok(*t),
            ExprKind::Error(None) => Err(AstError::UnknownTypeError),
            ExprKind::Number(_) => Ok(Type::Int64),
            ExprKind::Bool(_) => Ok(Type::Bool),
            ExprKind::Negate(e) => {
                if let Expr {
                    kind: _,
                    ty: Type::Int64,
                } = ***e
                {
                    Ok(Type::Int64)
                } else {
                    Err(type_error(Type::Int64, e))
                }
            }
            ExprKind::Op(e1, _, e2) => {
                if e1.ty != Type::Int64 {
                    Err(type_error(Type::Int64, e1))
                } else if e2.ty != Type::Int64 {
                    Err(type_error(Type::Int64, e2))
                } else {
                    Ok(e1.ty)
                }
            }
            ExprKind::If(c, t, f) => {
                if c.ty != Type::Bool {
                    Err(type_error(Type::Bool, c))
                } else if t.ty == f.ty {
                    Ok(t.ty)
                } else {
                    Err(type_error(Type::Int64, f))
                }
            }
            ExprKind::Sequence(v) => Ok(v[v.len() - 1].ty),
        }
    }

    /// Create an ExprKind::Error(Some(Type)) from a TypeError.
    /// For all other error types, return ExprKind::Error(None).
    pub fn from_error(error_recovery: &ErrorRecovery<'_>) -> ExprKind {
        match &error_recovery.error {
            ParseError::User {
                error:
                    Span {
                        item: AstError::TypeError { expected, .. },
                        ..
                    },
            } => ExprKind::Error(Some(*expected)),
            _ => ExprKind::Error(None),
        }
    }
}

fn type_error(expected: Type, found: &Expr) -> AstError {
    AstError::TypeError {
        expected,
        found: found.ty,
    }
}

pub fn parse(program: &str) -> Result<SpExpr, Vec<ParseError>> {
    let mut lexer = Lexer::new(program);
    let mut recovered_errors: Vec<ErrorRecovery<'_>> = Vec::new();
    let parser = grammar::ExpressionParser::new();
    let result: Result<SpExpr, ParseError> = parser.parse(&mut recovered_errors, &mut lexer);

    // convert lex errors into ParseError
    let mut errors: Vec<ParseError> = lexer
        .errors
        .into_iter()
        .map(|e| match e {
            LexError::InvalidToken((l, r)) => ParseError::UnrecognizedToken {
                token: (l, Token::Unexpected(&program[l..r]), r),
                expected: vec![],
            },
        })
        .collect();

    errors.append(&mut recovered_errors.into_iter().map(|r| r.error).collect());

    match result {
        Ok(expr) => {
            if errors.is_empty() {
                Ok(expr)
            } else {
                Err(errors)
            }
        }
        Err(e) => {
            // put the final error on the end of the error list presuming that
            // earlier lex errors or recovered errors were the root cause(s).
            errors.push(e);
            Err(errors)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::parse;
    use crate::ast::{AstError, Expr, ExprKind};
    use crate::span::Span;

    impl PartialEq for Span<AstError> {
        fn eq(&self, other: &Self) -> bool {
            **self == **other
        }
    }
    impl Eq for Span<AstError> {}

    macro_rules! expr {
        ($e:expr) => {
            Span {
                start: 0,
                end: 1,
                item: Expr::new($e).unwrap(),
            }
        };
    }

    macro_rules! parse_ok {
        ($s:literal) => {
            assert!(parse($s).is_ok())
        };
    }

    macro_rules! parse_fails {
        ($s:literal) => {
            assert!(parse($s).is_err())
        };
    }

    macro_rules! parses {
        ($($lhs:expr => $rhs:expr)+) => {{
             $(
                assert_eq!(Ok($rhs), parse($lhs).map(|b| b.item.kind));
             )+
        }};
    }

    #[test]
    fn numeric_operations() {
        parses! {
            "22" => ExprKind::Number("22".to_string())
            "(22)" => ExprKind::Number("22".to_string())
            "(((22)))" => ExprKind::Number("22".to_string())
        };
        parse_fails!("((22)");

        parse_ok!("1+2");
        parse_ok!("1-2");
        parse_ok!("1 * 2");
        parse_ok!("1 / 3");
        parse_ok!("1 + 2 * 3");

        // unary minus
        parse_ok!("-2");
        parse_ok!("4 * -2");
        parse_ok!("-(1+2)");
        parse_ok!("-(-(-1))");
        parse_ok!("3--2");
    }

    #[test]
    fn conditionals() {
        parses! {
            "true" => ExprKind::Bool(true)
            "false" => ExprKind::Bool(false)
            "if true { 1 } else { 2 }" => ExprKind::If(
                expr!(ExprKind::Bool(true)),
                expr!(ExprKind::Sequence(vec![expr!(ExprKind::Number("1".to_string()))])),
                expr!(ExprKind::Sequence(vec![expr!(ExprKind::Number("2".to_string()))])),
            )
            "if true { true;1 } else { 2 }" => ExprKind::If(
                expr!(ExprKind::Bool(true)),
                expr!(ExprKind::Sequence(vec![expr!(ExprKind::Bool(true)),
                                              expr!(ExprKind::Number("1".to_string()))])),
                expr!(ExprKind::Sequence(vec![expr!(ExprKind::Number("2".to_string()))])),
            )
        };

        // braces required
        parse_fails!("if true 1 else 0");
        // empty braces not allowed
        parse_fails!("if true {} else {0}");

        parse_ok!("if true {false} else {true}");
    }

    #[test]
    fn immediate_type_errors() {
        // `if` arms must match
        parse_fails!("if true {false} else {0}");
        parse_fails!("if true {1} else {true}");

        // math operators only accept numbers
        parse_fails!("true + 1");
        parse_fails!("1 + true");
        parse_fails!("true + true");
    }
}
