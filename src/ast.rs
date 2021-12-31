use crate::grammar;
use crate::lexer::{LexError, Lexer, Token};
use crate::span::Span;
use std::ops::Range;
use thiserror::Error;

///! This module is responsible for parsing source code into a validated AST
///! for later consumption by the compiler module.

pub type ParseError<'input> = lalrpop_util::ParseError<usize, Token<'input>, Span<AstError>>;
pub type ErrorRecovery<'input> = lalrpop_util::ErrorRecovery<usize, Token<'input>, Span<AstError>>;

/// Untyped Spanned syntax tree
pub type UntypedSpExpr = Span<Box<UntypedExpr>>;
pub type UntypedExprKind = ExprKind<UntypedSpExpr>;

// wrapper type to break cyclic type definition above
#[derive(Debug, PartialEq, Eq)]
pub struct UntypedExpr {
    kind: UntypedExprKind,
}

impl From<UntypedExprKind> for UntypedExpr {
    fn from(k: UntypedExprKind) -> Self {
        UntypedExpr { kind: k }
    }
}

impl From<UntypedExpr> for UntypedExprKind {
    fn from(e: UntypedExpr) -> Self {
        e.kind
    }
}

/// Typed Spanned syntax tree
pub type TypedSpExpr = Span<Box<Expr>>;
pub type TypedExprKind = ExprKind<TypedSpExpr>;

impl PartialEq for TypedSpExpr {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.ty == other.ty
    }
}
impl Eq for TypedSpExpr {}

impl PartialEq for UntypedSpExpr {
    fn eq(&self, other: &Self) -> bool {
        self.item == other.item
    }
}
impl Eq for UntypedSpExpr {}

/// ExprKind is used to build trees of untyped and typed expressions
#[derive(Debug, PartialEq, Eq)]
pub enum ExprKind<T> {
    Error(Option<Type>),
    Identifier(String),
    Number(String),
    Bool(bool),
    Negate(T),
    Op(T, Opcode, T),
    // condition, then-arm, else-arm
    If(T, T, T),
    // identifier, optional type, optional binding
    Let(String, Option<Type>, Option<T>),
    Block(Vec<T>),
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
    Void,
}

/// Typed Expression
#[derive(Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: TypedExprKind,
    pub ty: Type,
}

impl Expr {
    pub fn new(kind: TypedExprKind, ty: Type) -> Expr {
        Expr { kind, ty }
    }
}

/// convert an untyped expr tree into one with type information
impl From<UntypedExprKind> for Result<Box<Expr>, AstError> {
    fn from(kind: UntypedExprKind) -> Self {
        Ok(Box::new(kind.into_typed()?))
    }
}

impl From<(Type, TypedSpExpr)> for Expr {
    fn from((ty, sp): (Type, TypedSpExpr)) -> Self {
        Expr {
            kind: sp.item.kind,
            ty,
        }
    }
}

/// The Error type for anything that can go wrong during AST construction
/// including lexing, parsing, and type errors.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum AstError {
    #[error("{msg}")]
    Error { msg: String },
    #[error("expected {expected:?} but found {found:?}")]
    TypeError { expected: Type, found: Type },
    #[error("unknown type")]
    UnknownTypeError,
    #[error("unrecognized EOF")]
    UnrecognizedEOF,
    #[error("unexpected token \"{0}\". Expected one of: {1:?}")]
    UnexpectedToken(String, Vec<String>),
    #[error(transparent)]
    LexError(#[from] LexError),
}

impl From<Span<AstError>> for AstError {
    fn from(s: Span<AstError>) -> Self {
        s.item
    }
}

impl UntypedSpExpr {
    pub fn into_typed(self) -> Result<TypedSpExpr, Span<AstError>> {
        let typed = self.item.kind.into_typed();
        match typed {
            Ok(e) => Ok((self.start, Box::new(e), self.end).into()),
            Err(err) => Err((self.start, err, self.end).into()),
        }
    }
}

impl UntypedExprKind {
    /// Converts an untyped tree into a typed one, catching type errors in the process.
    pub fn into_typed(self) -> Result<Expr, AstError> {
        match self {
            // help the type checker recover from errors by letting the parser guess a type
            ExprKind::Error(Some(t)) => Ok(Expr::new(TypedExprKind::Error(Some(t)), t)),
            ExprKind::Error(None) => Err(AstError::UnknownTypeError),
            ExprKind::Number(s) => Ok(Expr::new(TypedExprKind::Number(s), Type::Int64)),
            ExprKind::Bool(b) => Ok(Expr::new(TypedExprKind::Bool(b), Type::Bool)),
            ExprKind::Negate(e) => match e.into_typed() {
                Ok(e) => {
                    if e.ty == Type::Int64 {
                        Ok(Expr::new(ExprKind::Negate(e), Type::Int64))
                    } else {
                        Err(type_error(Type::Int64, &e))
                    }
                }
                Err(error) => Err(error.into()),
            },
            ExprKind::Op(e1, op, e2) => {
                // TODO: we lose span information on the errors here.
                // To solve this, errors need to be chainable or embedded in the AST
                let e1 = e1.into_typed()?;
                let e2 = e2.into_typed()?;
                let ty = e1.ty;
                if e1.ty != Type::Int64 {
                    Err(type_error(ty, &e1))
                } else if e2.ty != Type::Int64 {
                    Err(type_error(ty, &e2))
                } else {
                    Ok(Expr::new(ExprKind::Op(e1, op, e2), ty))
                }
            }
            ExprKind::If(c, t, f) => {
                let c = c.into_typed()?;
                let t = t.into_typed()?;
                let f = f.into_typed()?;
                let ty = t.ty;
                if c.ty != Type::Bool {
                    Err(type_error(Type::Bool, &c))
                } else if t.ty == f.ty {
                    Ok(Expr::new(ExprKind::If(c, t, f), ty))
                } else {
                    Err(type_error(ty, &f))
                }
            }
            ExprKind::Block(exprs) => {
                // This could preserve more errors by accumulating all errors in the block.
                // The best way to do this might be to store AstError inside the Error node
                // so we automatically build error tree in case of errors.
                let mut typed_exprs = Vec::with_capacity(exprs.len());
                for expr in exprs {
                    match expr.into_typed() {
                        Ok(e) => typed_exprs.push(e),
                        Err(err) => return Err(err.into()),
                    }
                }
                let ty = if typed_exprs.is_empty() {
                    Type::Void
                } else {
                    typed_exprs[typed_exprs.len() - 1].ty
                };
                Ok(Expr::new(ExprKind::Block(typed_exprs), ty))
            }
            ExprKind::Identifier(i) => {
                // TODO: look up the identifier's type from the lexical type env (e.g. `let foo;`)
                // temporarily stub out Identifier types as Bool so the parser can be tested.
                Ok(Expr::new(ExprKind::Identifier(i), Type::Bool))
            }
            ExprKind::Let(i, ty, e) => {
                let e_typed = if let Some(e) = e {
                    Some(e.into_typed()?)
                } else {
                    None
                };

                if let Some(ty) = ty {
                    if let Some(e_ty) = e_typed {
                        if ty != e_ty.ty {
                            Err(type_error(ty, &e_ty))
                        } else {
                            Ok(Expr::new(ExprKind::Let(i, Some(ty), Some(e_ty)), ty))
                        }
                    } else {
                        Ok(Expr::new(ExprKind::Let(i, Some(ty), e_typed), ty))
                    }
                } else if let Some(expr) = e_typed {
                    let ty = expr.ty;
                    Ok(Expr::new(ExprKind::Let(i, Some(ty), Some(expr)), ty))
                } else {
                    // TODO: support type inference when an identifier is defined and later assigned.
                    Ok(Expr::new(
                        ExprKind::Let(i, Some(Type::Void), e_typed),
                        Type::Void,
                    ))
                }
            }
        }
    }
}

impl UntypedExprKind {
    /// Create an ExprKind::Error(Some(Type)) from a TypeError.
    /// For all other error types, return ExprKind::Error(None).
    pub fn from_error(error_recovery: &ErrorRecovery<'_>) -> UntypedExprKind {
        match &error_recovery.error {
            ParseError::User {
                error:
                    Span {
                        item: AstError::TypeError { expected, .. },
                        ..
                    },
            } => UntypedExprKind::Error(Some(*expected)),
            _ => UntypedExprKind::Error(None),
        }
    }
}

fn type_error(expected: Type, found: &TypedSpExpr) -> AstError {
    AstError::TypeError {
        expected,
        found: found.ty,
    }
}

pub fn parse(program: &str) -> Result<TypedSpExpr, Vec<Span<AstError>>> {
    let mut lexer = Lexer::new(program);
    let mut recovered_errors: Vec<ErrorRecovery<'_>> = Vec::new();

    let parser = grammar::ProgramParser::new();
    let result: Result<UntypedSpExpr, ParseError> = parser.parse(&mut recovered_errors, &mut lexer);

    // convert lex errors into AstError
    let mut errors: Vec<Span<AstError>> = lexer
        .errors
        .into_iter()
        .map(|e| match e {
            LexError::InvalidToken((l, r)) => Span {
                start: l,
                end: r,
                item: AstError::LexError(e),
            },
        })
        .collect();

    errors.append(
        &mut recovered_errors
            .into_iter()
            .map(|r| map_lalrpop_error(&r.error))
            .collect(),
    );

    match result {
        Ok(expr) => {
            if errors.is_empty() {
                // do type checking if there are no parse errors
                match expr.into_typed() {
                    Ok(exp) => Ok(exp),
                    Err(err) => {
                        errors.push(err);
                        Err(errors)
                    }
                }
            } else {
                Err(errors)
            }
        }
        Err(e) => {
            // put the final error on the end of the error list presuming that
            // earlier lex errors or recovered errors were the root cause(s).
            errors.push(map_lalrpop_error(&e));
            Err(errors)
        }
    }
}

fn map_lalrpop_error(error: &ParseError) -> Span<AstError> {
    match error {
        &ParseError::UnrecognizedEOF { location, .. } => {
            (location..location, AstError::UnrecognizedEOF)
        }
        &ParseError::InvalidToken { location } => (
            location..location,
            AstError::LexError(LexError::InvalidToken((location, location))),
        ),
        &ParseError::UnrecognizedToken {
            token,
            ref expected,
        } => (
            token.0..token.2,
            AstError::UnexpectedToken(token.1.to_string(), expected.to_vec()),
        ),
        &ParseError::ExtraToken { token } => (
            token.0..token.2,
            AstError::LexError(LexError::InvalidToken((token.0, token.2))),
        ),
        ParseError::User { error } => (Range::<usize>::from(error), error.item.clone()),
    }
    .into()
}

#[cfg(test)]
mod tests {
    use crate::ast::parse;
    use crate::ast::{AstError, ExprKind, UntypedExpr};
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
                item: Box::new(UntypedExpr { kind: $e }),
            }
        };
    }

    macro_rules! parse_ok {
        ($s:literal) => {
            let result = parse($s);
            assert!(result.is_ok(), "error: {:?}", result)
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
                assert_eq!($rhs.into_typed().unwrap().kind, parse($lhs).map(|b| b.item.kind).unwrap());
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
    fn identifiers() {
        parses! {
            "abc" => ExprKind::Identifier("abc".to_string())
            "a" => ExprKind::Identifier("a".to_string())
            "a123" => ExprKind::Identifier("a123".to_string())
        };
        parse_fails!("Caps");
    }

    #[test]
    fn conditionals() {
        parses! {
            "true" => ExprKind::Bool(true)
            "false" => ExprKind::Bool(false)
            "if true { 1 } else { 2 }" => ExprKind::If(
                expr!(ExprKind::Bool(true)),
                expr!(ExprKind::Block(vec![expr!(ExprKind::Number("1".to_string()))])),
                expr!(ExprKind::Block(vec![expr!(ExprKind::Number("2".to_string()))])),
            )
            "if true { true;1 } else { 2 }" => ExprKind::If(
                expr!(ExprKind::Bool(true)),
                expr!(ExprKind::Block(vec![expr!(ExprKind::Bool(true)),
                                              expr!(ExprKind::Number("1".to_string()))])),
                expr!(ExprKind::Block(vec![expr!(ExprKind::Number("2".to_string()))])),
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

    #[test]
    fn block() {
        parse_ok!("{ let foo = 1; }");
        parse_ok!("{ let foo = 1; true }");
        parse_ok!("{ if foo { 1 } else { 2 } }");
    }

    #[test]
    fn lexical_let() {
        parse_ok!("let foo = 1;");
        parse_ok!("let foo: int = 1;");
        parse_fails!("let foo = 1");

        parse_ok!("let foo = true; if foo { 1 } else { 2 }");
    }
}
