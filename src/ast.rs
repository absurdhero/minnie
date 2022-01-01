use crate::grammar;
use crate::lexer::{LexError, Lexer, Token};
use crate::span::Span;
use std::ops::Range;
use thiserror::Error;

///! This module is responsible for parsing source code into a validated AST
///! for consumption by the compiler module.

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
    Identifier(String),
    Number(String),
    Bool(bool),
    Negate(T),
    Op(T, Opcode, T),
    Block(Vec<T>),
    // condition, then-arm, else-arm
    If(T, T, T),
    // identifier, optional type, optional binding
    Let(String, Option<Type>, Option<T>),
    // The error and the original node (if present)
    Error(ErrorNode<T>),
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
    // can only exist in an AST that contains type errors
    Unknown,
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
    #[error("unrecognized EOF")]
    UnrecognizedEOF,
    #[error("unexpected token `{0}`. Expected one of: {1:?}")]
    UnexpectedToken(String, Vec<String>),
    #[error(transparent)]
    LexError(#[from] LexError),
    // // this variant stores an AST that contains one or more ExprKind::Error.
    // #[error("AST contains errors")]
    // InvalidAST(TypedSpExpr),
}

/// Records recoverable parse errors that still allow the AST
/// to be formed. It also tracks Type errors that occur
/// while converting the AST into a typed AST.
///
/// The first element is the type of error.
/// The second element is the AST node that this error applies to.
#[derive(Debug, PartialEq, Eq)]
pub struct ErrorNode<T> {
    pub kind: ErrorNodeKind,
    pub expr: Option<T>,
}
pub type TypedErrorNode = ErrorNode<TypedSpExpr>;

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum ErrorNodeKind {
    #[error("expected {expected:?} but found {found:?}")]
    TypeMismatch { expected: Type, found: Type },
    #[error("{0}")]
    TypeError(&'static str),
    #[error("unknown type")]
    UnknownType,
    #[error(transparent)]
    ParseError(AstError),
}

impl From<Span<AstError>> for AstError {
    fn from(s: Span<AstError>) -> Self {
        s.item
    }
}

impl UntypedSpExpr {
    /// Converts an untyped tree into a typed one, catching type errors in the process.
    pub fn into_typed(self) -> TypedSpExpr {
        let Span {
            start,
            end,
            item: untyped_exp,
        } = self;
        let typed_kind = match untyped_exp.kind {
            ExprKind::Error(ErrorNode {
                kind: err,
                expr: node,
            }) => {
                let typed_err_node = ErrorNode {
                    kind: err,
                    expr: node.map(|n| n.into_typed()),
                };
                match typed_err_node.kind {
                    // if the parser returns a TypeMismatch with an expected type,
                    // the type checker can use that to recover.
                    ErrorNodeKind::TypeMismatch { expected, found: _ } => {
                        Expr::new(TypedExprKind::Error(typed_err_node), expected)
                    }
                    // Otherwise, set the expression's type to Unknown.
                    _ => Expr::new(TypedExprKind::Error(typed_err_node), Type::Unknown),
                }
            }
            ExprKind::Number(s) => Expr::new(TypedExprKind::Number(s), Type::Int64),
            ExprKind::Bool(b) => Expr::new(TypedExprKind::Bool(b), Type::Bool),
            ExprKind::Negate(e) => {
                let mut e = e.into_typed();
                if e.ty != Type::Int64 {
                    e = type_error_correction(Type::Int64, e);
                }
                Expr::new(ExprKind::Negate(e), Type::Int64)
            }
            ExprKind::Op(e1, op, e2) => {
                let mut e1 = e1.into_typed();
                let mut e2 = e2.into_typed();
                let expected = Type::Int64;
                if e1.ty != Type::Int64 {
                    e1 = type_error_correction(expected, e1);
                }
                if e2.ty != Type::Int64 {
                    e2 = type_error_correction(expected, e2);
                }
                Expr::new(ExprKind::Op(e1, op, e2), expected)
            }
            ExprKind::If(c, t, f) => {
                let mut c = c.into_typed();
                let t = t.into_typed();
                let mut f = f.into_typed();
                let return_ty = t.ty;
                if c.ty != Type::Bool {
                    c = type_error_correction(Type::Bool, c)
                }
                if f.ty != return_ty {
                    f = type_error_correction(return_ty, f);
                    return type_error_annotation(
                        TypedSpExpr::new(start, end, ExprKind::If(c, t, f), return_ty),
                        "the branches of this `if` condition have mismatched return types",
                    );
                }
                Expr::new(ExprKind::If(c, t, f), return_ty)
            }
            ExprKind::Block(exprs) => {
                let typed_exprs: Vec<TypedSpExpr> =
                    exprs.into_iter().map(UntypedSpExpr::into_typed).collect();
                let ty = if typed_exprs.is_empty() {
                    Type::Void
                } else {
                    typed_exprs[typed_exprs.len() - 1].ty
                };
                Expr::new(ExprKind::Block(typed_exprs), ty)
            }
            ExprKind::Identifier(i) => {
                // TODO: look up the identifier's type from the lexical type env (e.g. `let foo;`)
                // temporarily stub out Identifier types as Bool so the parser can be tested.
                Expr::new(ExprKind::Identifier(i), Type::Bool)
            }
            ExprKind::Let(i, ty, e) => {
                let binding = e.map(|e| e.into_typed());

                if let Some(ty) = ty {
                    if let Some(mut bind_expr) = binding {
                        if ty != bind_expr.ty {
                            bind_expr = type_error_correction(ty, bind_expr)
                        }
                        Expr::new(ExprKind::Let(i, Some(ty), Some(bind_expr)), ty)
                    } else {
                        Expr::new(ExprKind::Let(i, Some(ty), binding), ty)
                    }
                } else if let Some(expr) = binding {
                    let ty = expr.ty;
                    Expr::new(ExprKind::Let(i, Some(ty), Some(expr)), ty)
                } else {
                    // TODO: support type inference when an identifier is defined and later assigned.
                    Expr::new(ExprKind::Let(i, Some(Type::Void), binding), Type::Void)
                }
            }
        };
        (self.start, Box::new(typed_kind), self.end).into()
    }
}

impl UntypedExprKind {
    // called by the lalrpop grammar to record recovery actions
    pub fn from_error(error_recovery: &ErrorRecovery<'_>) -> UntypedExprKind {
        UntypedExprKind::Error(ErrorNode {
            kind: ErrorNodeKind::ParseError(map_lalrpop_error(&error_recovery.error).item),
            expr: None,
        })
    }
}

fn type_error_correction(expected: Type, found: TypedSpExpr) -> TypedSpExpr {
    Span {
        start: found.start,
        end: found.end,
        item: Box::new(Expr {
            kind: ExprKind::Error(ErrorNode {
                kind: ErrorNodeKind::TypeMismatch {
                    expected,
                    found: found.ty,
                },
                expr: Some(found),
            }),
            // pretend that we got the expected type so we can press on with type analysis
            ty: expected,
        }),
    }
}

fn type_error_annotation(expr: TypedSpExpr, msg: &'static str) -> TypedSpExpr {
    let ty = expr.ty.clone();
    Span {
        start: expr.start,
        end: expr.end,
        item: Box::new(Expr {
            kind: ExprKind::Error(ErrorNode {
                kind: ErrorNodeKind::TypeError(msg),
                expr: Some(expr),
            }),
            ty,
        }),
    }
}

impl TypedSpExpr {
    fn new(start: usize, end: usize, expr: ExprKind<TypedSpExpr>, ty: Type) -> TypedSpExpr {
        Span {
            start,
            end,
            item: Box::new(Expr { kind: expr, ty }),
        }
    }

    /// Get a list of the errors encountered when descending the tree.
    ///
    /// Errors are returned in bottom-up order except when roots_only
    /// is set in which case they are returned in the order of the source text.
    ///
    /// # Arguments
    /// * `roots_only` - Return only the shallowest, broadest errors. Useful for finding
    ///    groups of related errors to report separately to the user.
    pub fn errors<'a>(
        &'a self,
        roots_only: bool,
    ) -> Box<dyn Iterator<Item = &'a TypedErrorNode> + 'a> {
        match &self.kind {
            TypedExprKind::Error(node) => match &node.expr {
                None => Box::new(std::iter::once(node)),
                Some(expr) => {
                    if roots_only {
                        Box::new(std::iter::once(node))
                    } else {
                        Box::new(
                            expr.errors(roots_only)
                                .chain(Box::new(std::iter::once(node))),
                        )
                    }
                }
            },
            TypedExprKind::Identifier(_) | TypedExprKind::Number(_) | TypedExprKind::Bool(_) => {
                Box::new(std::iter::empty())
            }
            TypedExprKind::Negate(e) => e.errors(roots_only),
            TypedExprKind::Op(a, _, b) => {
                Box::new(a.errors(roots_only).chain(b.errors(roots_only)))
            }
            TypedExprKind::If(c, t, f) => Box::new(
                c.errors(roots_only)
                    .chain(t.errors(roots_only))
                    .chain(f.errors(roots_only)),
            ),
            TypedExprKind::Let(_, _, e) => match e {
                None => Box::new(std::iter::empty()),
                Some(e) => e.errors(roots_only),
            },
            TypedExprKind::Block(v) => v
                .iter()
                .map(|expr| expr.errors(roots_only))
                .fold(Box::new(std::iter::empty()), |i, b| Box::new(i.chain(b))),
        }
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
                Ok(expr.into_typed())
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
            assert!(result.is_ok(), "error: {:?}", result);
            assert!(
                parse($s).unwrap().errors(true).next().is_none(),
                "error expected but parse succeeded: {:?}",
                $s
            );
        };
    }

    macro_rules! parse_fails {
        ($s:literal) => {
            assert!(parse($s).is_err())
        };
    }

    macro_rules! ast_error {
        ($s:literal) => {
            assert!(
                !parse($s).unwrap().errors(true).next().is_none(),
                "no errors in AST for expression: {:?}",
                $s
            )
        };
    }

    macro_rules! parses {
        ($($lhs:expr => $rhs:expr)+) => {{
             $(
                assert_eq!($rhs.into_typed().kind, parse($lhs).map(|b| b.item.kind).unwrap());
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

        parse_ok!("if true {false} else {true}");
        // braces required
        parse_fails!("if true 1 else 0");
        // empty braces are legal and return Type::Void.
        parse_ok!("if true {} else {}");
        // Syntax OK but type checking fails.
        ast_error!("if true {} else {0}");
    }

    #[test]
    fn immediate_type_errors() {
        // `if` arms must match
        ast_error!("if true {false} else {0}");
        ast_error!("if true {1} else {true}");

        // math operators only accept numbers
        ast_error!("true + 1");
        ast_error!("1 + true");
        ast_error!("true + true");
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
