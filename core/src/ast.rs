use crate::grammar;
use crate::lexer::{LexError, Lexer, Token};
use crate::span::Span;
use std::collections::HashMap;
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
    Identifier(ID),
    Number(String),
    Bool(bool),
    Negate(T),
    Op(T, Opcode, T),
    Call(T, Vec<T>),
    Block(Vec<T>),
    // condition, then-arm, else-arm
    If(T, T, T),
    // identifier, optional type, optional binding
    Let(ID, Option<Type>, Option<T>),
    // The error and the original node (if present)
    Error(ErrorNode<T>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ID {
    Name(String),
    Id(usize),
}
impl ID {
    // unsafe accessors used in distinct AST phases.
    pub fn name(&self) -> &String {
        if let ID::Name(name) = self {
            name
        } else {
            panic!("accessed textual ID on resolved numeric ID");
        }
    }
    pub fn id(&self) -> usize {
        if let ID::Id(id) = self {
            *id
        } else {
            panic!("accessed numeric ID on unresolved textual ID");
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Opcode {
    Mul,
    Div,
    Add,
    Sub,
}

/// Types supported by the language
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    // Primitive Types
    Int64,
    Bool,
    Void,

    // Compound Types
    Function{
        params: Vec<Type>,
        returns: Box<Type>,
    },

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
    #[error("unknown identifier `{0}`")]
    UnknownIdentifier(String),
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
    pub fn into_typed(self, lexical_env: &mut LexicalEnv) -> TypedSpExpr {
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
                let err_type = match err {
                    // if the parser returns a TypeMismatch with an expected type,
                    // the type checker can use that to recover.
                    ErrorNodeKind::TypeMismatch { ref expected, found: _ } => expected.clone(),
                    // Otherwise, set the expression's type to Unknown.
                    _ => Type::Unknown,
                };
                let typed_err_node = ErrorNode {
                    kind: err,
                    expr: node.map(|n| n.into_typed(lexical_env)),
                };
                Expr::new(TypedExprKind::Error(typed_err_node), err_type)
            }
            ExprKind::Number(s) => Expr::new(TypedExprKind::Number(s), Type::Int64),
            ExprKind::Bool(b) => Expr::new(TypedExprKind::Bool(b), Type::Bool),
            ExprKind::Negate(e) => {
                let mut e = e.into_typed(lexical_env);
                if e.ty != Type::Int64 {
                    e = type_error_correction(Type::Int64, e);
                }
                Expr::new(ExprKind::Negate(e), Type::Int64)
            }
            ExprKind::Op(e1, op, e2) => {
                let mut e1 = e1.into_typed(lexical_env);
                let mut e2 = e2.into_typed(lexical_env);
                if e1.ty != Type::Int64 {
                    e1 = type_error_correction(Type::Int64, e1);
                }
                if e2.ty != Type::Int64 {
                    e2 = type_error_correction(Type::Int64, e2);
                }
                Expr::new(ExprKind::Op(e1, op, e2), Type::Int64)
            }
            ExprKind::Call(op, params) => {
                let typed_op = op.into_typed(lexical_env);
                let func_type = typed_op.ty.clone();
                let typed_actuals: Vec<TypedSpExpr> = params
                    .into_iter()
                    .map(|e| e.into_typed(lexical_env))
                    .collect();
                let actual_types: Vec<Type> = typed_actuals.iter().map(|p| p.ty.clone()).collect();

                // verify that func_type is a Function and that the arguments
                // match the formal parameters.
                match func_type {
                    Type::Function { params: formal_params, returns } => {

                        // TODO: compare length and then zip so multiple errors can be omitted for mismatched params.
                        if actual_types == formal_params {
                            // The type of this expression is the return type of
                            // the function after evaluation.
                            Expr::new(ExprKind::Call(typed_op, typed_actuals), returns.as_ref().clone())
                        } else {
                            // broken
                            let typed_op = type_error_correction(Type::Unknown, typed_op);
                            Expr::new(ExprKind::Call(typed_op, typed_actuals), returns.as_ref().clone())
                        }
                    }
                    _ => {
                         // if it isn't a function, return a corrected return type
                        let typed_op = type_error_correction(Type::Unknown, typed_op);
                        Expr::new(ExprKind::Call(typed_op, typed_actuals), Type::Unknown)
                    }
                }
            }
            ExprKind::If(c, t, f) => {
                let mut c = c.into_typed(lexical_env);
                let t = t.into_typed(lexical_env);
                let mut f = f.into_typed(lexical_env);
                let return_ty = t.ty.clone();
                if c.ty != Type::Bool {
                    c = type_error_correction(Type::Bool, c)
                }
                if f.ty != return_ty {
                    f = type_error_correction(return_ty.clone(), f);
                    return type_error_annotation(
                        TypedSpExpr::new(start, end, ExprKind::If(c, t, f), return_ty),
                        "the branches of this `if` condition have mismatched return types",
                    );
                }
                Expr::new(ExprKind::If(c, t, f), return_ty.clone())
            }
            ExprKind::Block(exprs) => {
                let mut block_env = LexicalEnv::new(lexical_env);
                let typed_exprs: Vec<TypedSpExpr> = exprs
                    .into_iter()
                    .map(|e| e.into_typed(&mut block_env))
                    .collect();
                let ty = if typed_exprs.is_empty() {
                    Type::Void
                } else {
                    typed_exprs[typed_exprs.len() - 1].ty.clone()
                };
                Expr::new(ExprKind::Block(typed_exprs), ty)
            }
            ExprKind::Identifier(i) => {
                if let Some((id, ty)) = lexical_env.id_type(i.name()) {
                    Expr::new(ExprKind::Identifier(id), ty)
                } else {
                    return type_error(
                        ErrorNode {
                            kind: ErrorNodeKind::UnknownIdentifier(i.name().clone()),
                            expr: Some(TypedSpExpr::new(
                                start,
                                end,
                                ExprKind::Identifier(i),
                                Type::Unknown,
                            )),
                        },
                        start..end,
                        Type::Unknown,
                    );
                }
            }
            ExprKind::Let(id, ty, e) => {
                let binding = e.map(|e| e.into_typed(lexical_env));

                if let Some(ty) = ty {
                    let uid = lexical_env.add(id.name(), ty.clone());
                    if let Some(mut bind_expr) = binding {
                        if ty != bind_expr.ty {
                            bind_expr = type_error_correction(ty.clone(), bind_expr)
                        }
                        Expr::new(ExprKind::Let(uid, Some(ty), Some(bind_expr)), Type::Void)
                    } else {
                        Expr::new(ExprKind::Let(uid, Some(ty), binding), Type::Void)
                    }
                } else if let Some(expr) = binding {
                    let ty = &expr.ty;
                    let uid = lexical_env.add(id.name(), ty.clone());
                    Expr::new(ExprKind::Let(uid, Some(ty.clone()), Some(expr)), Type::Void)
                } else {
                    return type_error_annotation(
                        TypedSpExpr::new(
                            start,
                            end,
                            ExprKind::Let(id, Some(Type::Void), binding),
                            Type::Void,
                        ),
                        "Not supported: untyped `let` with no binding.",
                    );
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

fn type_error(error: TypedErrorNode, span: Range<usize>, new_type: Type) -> TypedSpExpr {
    Span {
        start: span.start,
        end: span.end,
        item: Box::new(Expr {
            kind: ExprKind::Error(error),
            ty: new_type,
        }),
    }
}

fn type_error_correction(expected: Type, found: TypedSpExpr) -> TypedSpExpr {
    let range = found.range();
    type_error(
        ErrorNode {
            kind: ErrorNodeKind::TypeMismatch {
                expected: expected.clone(),
                found: found.ty.clone(),
            },
            expr: Some(found),
        },
        range,
        expected,
    )
}

fn type_error_annotation(expr: TypedSpExpr, msg: &'static str) -> TypedSpExpr {
    let ty = expr.ty.clone();
    let range = expr.range();
    type_error(
        ErrorNode {
            kind: ErrorNodeKind::TypeError(msg),
            expr: Some(expr),
        },
        range,
        ty,
    )
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
            TypedExprKind::Op(l, _, r) => {
                Box::new(l.errors(roots_only).chain(r.errors(roots_only)))
            }
            TypedExprKind::Call(op, params) => Box::new(op.errors(roots_only).chain(
                params.iter().map(|expr| expr.errors(roots_only)).fold(
                    Box::new(std::iter::empty())
                        as Box<dyn Iterator<Item = &'a TypedErrorNode> + 'a>,
                    |i, b| Box::new(i.chain(b)),
                ),
            )),

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

    /// Find locally bound identifiers and place their Type in a vector indexed by their ID number
    pub fn local_identifiers(&self, local: &mut Vec<Type>) {
        let ty = &self.ty;
        match &self.kind {
            TypedExprKind::Identifier(id) => match id {
                ID::Id(id) => {
                    if local.len() <= *id {
                        local.resize(id + 1, Type::Unknown);
                    }
                    local[*id] = ty.clone();
                }
                ID::Name(_) => {
                    panic!("local_identifiers called on an untransformed tree")
                }
            },
            TypedExprKind::Negate(e) => e.local_identifiers(local),
            TypedExprKind::Op(l, _, r) => {
                l.local_identifiers(local);
                r.local_identifiers(local)
            }
            TypedExprKind::Block(exprs) => {
                for e in exprs {
                    e.local_identifiers(local);
                }
            }
            TypedExprKind::If(c, t, f) => {
                c.local_identifiers(local);
                t.local_identifiers(local);
                f.local_identifiers(local)
            }
            TypedExprKind::Let(id, _, e) => {
                if let Some(e) = e {
                    // for `let id = expr`, the id is accessed while binding.
                    // Dead store elimination would obviate this need.
                    match id {
                        ID::Id(id) => {
                            if local.len() <= *id {
                                local.resize(id + 1, Type::Unknown);
                            }
                            local[*id] = e.ty.clone();
                        }
                        ID::Name(_) => {
                            panic!("local_identifiers called on an untransformed tree")
                        }
                    }
                    e.local_identifiers(local);
                }
            }
            _ => {}
        }
    }
}

impl<T> ExprKind<T> {
    pub fn is_expression(&self) -> bool {
        !matches!(self, ExprKind::Let(_, _, _) | ExprKind::Error(_))
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
                let mut env = LexicalEnv::new_root();
                Ok(expr.into_typed(&mut env))
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

pub struct LexicalEnv<'a> {
    // association of symbol to its unique ID and type
    bindings: HashMap<String, (ID, Type)>,
    parent: Option<&'a LexicalEnv<'a>>,
}

impl<'a> LexicalEnv<'a> {
    fn new(parent: &'a LexicalEnv) -> LexicalEnv<'a> {
        LexicalEnv {
            bindings: HashMap::new(),
            parent: Some(parent),
        }
    }

    fn new_root() -> LexicalEnv<'a> {
        LexicalEnv {
            bindings: HashMap::new(),
            parent: None,
        }
    }

    fn add(&mut self, name: &str, ty: Type) -> ID {
        let new_id = ID::Id(self.next_id());
        self.bindings.insert(name.to_string(), (new_id.clone(), ty));
        new_id
    }

    fn next_id(&self) -> usize {
        self.bindings.len() + self.parent.map_or(0, |p| p.next_id())
    }

    fn id_type(&self, name: &str) -> Option<(ID, Type)> {
        self.bindings
            .get(name)
            .cloned()
            .or_else(|| self.parent.and_then(|p| p.id_type(name)))
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{parse, UntypedExprKind, UntypedSpExpr};
    use crate::ast::{AstError, ExprKind, LexicalEnv, UntypedExpr, ID};
    use crate::span::Span;

    impl PartialEq for Span<AstError> {
        fn eq(&self, other: &Self) -> bool {
            **self == **other
        }
    }
    impl Eq for Span<AstError> {}

    impl From<UntypedExprKind> for UntypedSpExpr {
        fn from(k: UntypedExprKind) -> Self {
            (0, Box::new(UntypedExpr::from(k)), 0).into()
        }
    }

    macro_rules! expr {
        ($e:expr) => {
            Span {
                start: 0,
                end: 1,
                item: Box::new(UntypedExpr { kind: $e }),
            }
        };
    }

    macro_rules! block {
        [$e:expr $(, $rest:expr)*] => {
            expr!(ExprKind::Block(vec![
                $e $(, $rest)*
            ]))
        };
    }

    macro_rules! parse_ok {
        ($s:literal) => {
            let result = parse($s);
            assert!(result.is_ok(), "error: {:?}", result);
            let parse_result = parse($s).unwrap();
            let error = parse_result.errors(true).next();
            assert!(
                error.is_none(),
                "parse error in: {:?}: {:#?}",
                $s,
                error.unwrap()
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
            let mut env = LexicalEnv::new_root();
             $(
                assert_eq!(UntypedSpExpr::from($rhs).into_typed(&mut env).kind, parse($lhs).map(|b| b.item.kind).unwrap());
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
            "abc" => ExprKind::Identifier(ID::Name("abc".to_string()))
            "a" => ExprKind::Identifier(ID::Name("a".to_string()))
            "a123" => ExprKind::Identifier(ID::Name("a123".to_string()))
        };
        parse_fails!("Caps");
    }

    #[test]
    fn conditionals() {
        let one = || expr!(ExprKind::Number("1".to_string()));
        let two = || expr!(ExprKind::Number("2".to_string()));

        parses! {
            "true" => ExprKind::Bool(true)
            "false" => ExprKind::Bool(false)
            "if true { 1 } else { 2 }" => ExprKind::If(
                expr!(ExprKind::Bool(true)),
                block![one()],
                block![two()],
            )
            "if true { true;1 } else { 2 }" => ExprKind::If(
                expr!(ExprKind::Bool(true)),
                block![expr!(ExprKind::Bool(true)), one()],
                block![two()],
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
    fn lexical_block() {
        parse_ok!("{ let foo = 1; }");
        parse_ok!("{ let foo = 1; true }");
        parse_ok!("{ if true { let foo = 1; foo } else { 2 } }");
        parse_ok!("{{ let foo = 1;} { 1 } }");

        // foo not defined in scope
        ast_error!("{ if foo { 1 } else { 2 } }");
        ast_error!("{ if true { let foo = 1; foo } else { foo } }");
        ast_error!("{{ let foo = 1;} { foo } }");

        // cases where a block must not be treated as a sub-expression
        // and should be treated as an element in a sequence of expressions instead.
        let one = || expr!(ExprKind::Number("1".to_string()));
        parses! {
            "{1}-1" => block![block![one()], expr!(ExprKind::Negate(one()))]
            "{1}(1)" => block![block![one()], one()]
        };
    }

    #[test]
    fn lexical_let() {
        parse_ok!("let foo = 1;");
        parse_ok!("let foo: int = 1;");
        // missing semicolon
        parse_fails!("let foo = 1");

        // test type inference
        parse_ok!("let foo = true; if foo { 1 } else { 2 }");
        parse_ok!("let foo = 1; if true { foo } else { 2 }");

        parse_ok!("let foo:int = 1; foo");
        ast_error!("let foo:bool = 1; foo");
    }

    #[test]
    fn call() {
        parses! {
            "foo()" => ExprKind::Call(expr!(ExprKind::Identifier(ID::Name("foo".to_string()))), vec![])
            "foo()();" => ExprKind::Call(expr!(
                ExprKind::Call(expr!(ExprKind::Identifier(ID::Name("foo".to_string()))), vec![])),
                vec![])
        };
    }
}
