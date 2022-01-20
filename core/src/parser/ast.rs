use super::lexical_env::LexicalEnv;
use crate::lexer::{LexError, Token};
use crate::module::ModuleEnv;
use crate::span::Span;
use crate::symbols::Symbol;
use crate::types::{Type, ID};
use itertools::Itertools;
use std::ops::Range;
use thiserror::Error;

#[cfg(feature = "serialize_ast")]
use serde::Serialize;

///! This module is responsible for parsing source code into a validated AST
///! for consumption by the compiler module.

/// These Error types are only used by `grammar.lalrpop`.
/// They are converted to our own error types for consumers of this module.
pub type ParseError<'input> = lalrpop_util::ParseError<usize, Token<'input>, Span<AstError>>;
pub type ErrorRecovery<'input> = lalrpop_util::ErrorRecovery<usize, Token<'input>, Span<AstError>>;

/// Untyped Spanned syntax tree
pub type UntypedSpExpr = Span<Box<UntypedExpr>>;
pub type UntypedExprKind = ExprKind<UntypedSpExpr>;

// wrapper type to break cyclic type definition above
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize_ast", derive(Serialize))]
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
#[cfg_attr(feature = "serialize_ast", derive(Serialize))]
pub enum ExprKind<T> {
    Identifier(ID),
    Number(String),
    Bool(bool),
    Negate(T),
    CompareOp(T, CompareOp, T),
    ArithOp(T, ArithOp, T),
    Call(T, Vec<T>),
    Block(Vec<T>),
    // fields: name, params, return type, body
    Function(FuncExpr<T>),
    // fields: condition, then-arm, else-arm
    If(T, T, T),
    // fields: identifier, optional type, optional binding
    Let(ID, Option<Type>, Option<T>),
    // The error and the original node (if present)
    Error(ErrorNode<T>),
}

impl<T> ExprKind<T> {
    pub fn is_expression(&self) -> bool {
        !matches!(self, ExprKind::Let(_, _, _) | ExprKind::Error(_))
    }
}

#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize_ast", derive(Serialize))]
pub enum ArithOp {
    Mul,
    Div,
    Add,
    Sub,
}

#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize_ast", derive(Serialize))]
pub enum CompareOp {
    Eq,
    Neq,
    Lt,
    Gt,
    LtEq,
    GtEq,
}

#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize_ast", derive(Serialize))]
pub struct FuncExpr<T> {
    pub id: ID,
    pub name: Symbol,
    pub params: Vec<FormalParam>,
    pub returns: Type,
    pub body: T,
}

impl<T> FuncExpr<T> {
    pub fn new(
        name: Symbol,
        id: ID,
        params: Vec<FormalParam>,
        returns: Type,
        body: T,
    ) -> FuncExpr<T> {
        FuncExpr {
            name,
            id,
            params,
            returns,
            body,
        }
    }
}

/// A parameter declaration in a function signature.
///
/// The representation will need to change once pattern arguments are supported.
/// The `name` field will be replaced by a pattern expression and a new AST
/// transformation will replace the pattern with unnamed local variable ID and
/// insert destructuring expressions into the AST at the beginning of the function's block.
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize_ast", derive(Serialize))]
pub struct FormalParam {
    pub name: ID,
    pub ty: Type,
}

/// Typed Expression
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize_ast", derive(Serialize))]
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
#[cfg_attr(feature = "serialize_ast", derive(Serialize))]
pub enum AstError {
    #[error("unrecognized EOF")]
    UnrecognizedEOF,
    #[error("unexpected token `{0}`. Expected one of: {}", .1.join(", "))]
    UnexpectedToken(String, Vec<String>),
    #[error(transparent)]
    LexError(#[from] LexError),
}

/// Records recoverable parse errors that still allow the AST
/// to be formed. It also tracks Type errors that occur
/// while converting the AST into a typed AST.
///
/// The first element is the type of error.
/// The second element is the AST node that this error applies to.
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize_ast", derive(Serialize))]
pub struct ErrorNode<T> {
    pub kind: ErrorNodeKind,
    pub expr: Option<T>,
}
pub type TypedErrorNode = ErrorNode<TypedSpExpr>;

#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serialize_ast", derive(Serialize))]
pub enum ErrorNodeKind {
    #[error("expected {expected} but found {found}")]
    TypeMismatch { expected: Type, found: Type },
    #[error("{0}")]
    TypeError(String),
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
    /// Converts an untyped tree into a typed one.
    ///
    /// # Work Performed During This Phase
    ///
    /// * tracking the declaration of variables and functions
    /// * converting identifiers into unique ID numbers
    /// * annotating the AST with type errors
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
                    ErrorNodeKind::TypeMismatch {
                        ref expected,
                        found: _,
                    } => expected.clone(),
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
                let e = e.assert_type(lexical_env, Type::Int64);
                Expr::new(ExprKind::Negate(e), Type::Int64)
            }
            ExprKind::CompareOp(l, op, r) => {
                let l = l.into_typed(lexical_env);
                let r = r.assert_type(lexical_env, l.ty.clone());
                Expr::new(ExprKind::CompareOp(l, op, r), Type::Bool)
            }
            ExprKind::ArithOp(l, op, r) => {
                let l = l.assert_type(lexical_env, Type::Int64);
                let r = r.assert_type(lexical_env, Type::Int64);
                Expr::new(ExprKind::ArithOp(l, op, r), Type::Int64)
            }
            ExprKind::Call(op, args) => {
                let typed_op = op.into_typed(lexical_env);
                let oper_type = typed_op.ty.clone();

                // verify that func_type is a Function and that the arguments
                // match the formal parameters.
                match oper_type {
                    Type::Function {
                        params: formal_params,
                        returns,
                    } => {
                        let actual_len = args.len();

                        let verified_actuals = args
                            .into_iter()
                            .zip_longest(formal_params.clone())
                            // ignore too few arguments. Make a single error for that below.
                            .filter(|z| !z.is_right())
                            .map(|z| {
                                if z.is_both() {
                                    let (actual, formal) = z.both().unwrap();
                                    actual.assert_type(lexical_env, formal)
                                } else {
                                    // z.is_left() -- too many arguments
                                    type_error_annotation(
                                        z.left().unwrap().into_typed(lexical_env),
                                        format!(
                                            "this function takes {} arguments but {} were supplied",
                                            formal_params.len(),
                                            actual_len
                                        ),
                                    )
                                }
                            })
                            .collect::<Vec<TypedSpExpr>>();
                        // now handle the case where there weren't enough arguments
                        if actual_len < formal_params.len() {
                            return type_error_annotation(
                                TypedSpExpr::new(
                                    start,
                                    end,
                                    ExprKind::Call(typed_op, verified_actuals),
                                    returns.as_ref().clone(),
                                ),
                                format!(
                                    "this function takes {} arguments but {} were supplied",
                                    formal_params.len(),
                                    actual_len
                                ),
                            );
                        } else {
                            Expr::new(
                                ExprKind::Call(typed_op, verified_actuals),
                                returns.as_ref().clone(),
                            )
                        }
                    }
                    _ => {
                        // if the operator isn't a function, return a corrected return type
                        // and guess what kind of function was expected.
                        let typed_actuals: Vec<TypedSpExpr> = args
                            .into_iter()
                            .map(|p| p.into_typed(lexical_env))
                            .collect();
                        let expected = Type::Function {
                            params: typed_actuals.iter().map(|a| a.ty.clone()).collect(),
                            returns: Box::new(Type::Unknown),
                        };
                        let typed_op = type_error_correction(expected, typed_op);
                        Expr::new(ExprKind::Call(typed_op, typed_actuals), Type::Unknown)
                    }
                }
            }
            ExprKind::If(c, t, f) => {
                let c = c.assert_type(lexical_env, Type::Bool);
                let t = t.into_typed(lexical_env);
                let mut f = f.into_typed(lexical_env);
                let return_ty = t.ty.clone();
                if f.ty != return_ty {
                    f = type_error_correction(return_ty.clone(), f);
                    return type_error_annotation(
                        TypedSpExpr::new(start, end, ExprKind::If(c, t, f), return_ty),
                        "the branches of this `if` condition have mismatched return types"
                            .to_string(),
                    );
                }
                Expr::new(ExprKind::If(c, t, f), return_ty)
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
                if let Some((id, ty)) = lexical_env.id_type(i.symbol()) {
                    Expr::new(ExprKind::Identifier(id), ty)
                } else {
                    return type_error(
                        ErrorNode {
                            kind: ErrorNodeKind::UnknownIdentifier(i.to_string()),
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
                    let uid = lexical_env.add_var(id.symbol(), &ty);
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
                    let uid = lexical_env.add_var(id.symbol(), ty);
                    Expr::new(ExprKind::Let(uid, Some(ty.clone()), Some(expr)), Type::Void)
                } else {
                    return type_error_annotation(
                        TypedSpExpr::new(
                            start,
                            end,
                            ExprKind::Let(id, Some(Type::Void), binding),
                            Type::Void,
                        ),
                        "Not supported: untyped `let` with no binding.".to_string(),
                    );
                }
            }
            UntypedExprKind::Function(FuncExpr {
                name,
                id,
                params,
                returns,
                body,
            }) => {
                // add the name to the environment
                let id = lexical_env.add_func(&id, Type::Unknown);

                // create a new lexical environment for the function body
                let mut func_env = LexicalEnv::new(lexical_env);

                // register and track the IDs of each parameter
                let typed_params: Vec<FormalParam> = params
                    .into_iter()
                    .map(|p| FormalParam {
                        name: func_env.add_var(p.name.symbol(), &p.ty),
                        ty: p.ty,
                    })
                    .collect();

                // generate the type signature of this function
                let func_ty = Type::Function {
                    params: typed_params.iter().map(|p| p.ty.clone()).collect(),
                    returns: Box::new(returns.clone()),
                };

                // fill in the outer environment with the function's fully resolved type
                if matches!(id, ID::FuncId(_)) {
                    lexical_env.update_func(&name, func_ty.clone());
                }

                // It would be better if we could point out the specific return expression
                // that didn't match instead of highlighting the whole body as wrong.
                // This would require passing the expected return type down into the block.
                let typed_body = body.assert_type(&mut func_env, returns.clone());

                // return the typed function
                Expr::new(
                    ExprKind::Function(FuncExpr {
                        name,
                        id,
                        params: typed_params,
                        returns,
                        body: typed_body,
                    }),
                    func_ty,
                )
            }
        };
        (self.start, Box::new(typed_kind), self.end).into()
    }

    /// converts an untyped expr into a typed one and checks that it is the expected type.
    ///
    /// If the type doesn't match, it wraps the expr in an ErrorNode
    /// and sets it to the desired type so parsing may continue.
    fn assert_type(self, lexical_env: &mut LexicalEnv, expected: Type) -> TypedSpExpr {
        let typed = self.into_typed(lexical_env);
        if typed.ty != expected {
            type_error_correction(expected, typed)
        } else {
            typed
        }
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

fn type_error_annotation(expr: TypedSpExpr, msg: String) -> TypedSpExpr {
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
    pub fn new(start: usize, end: usize, expr: ExprKind<TypedSpExpr>, ty: Type) -> TypedSpExpr {
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
            TypedExprKind::CompareOp(l, _, r) | TypedExprKind::ArithOp(l, _, r) => {
                Box::new(l.errors(roots_only).chain(r.errors(roots_only)))
            }
            TypedExprKind::Call(op, params) => Box::new(op.errors(roots_only).chain(
                params.iter().map(|expr| expr.errors(roots_only)).fold(
                    Box::new(std::iter::empty())
                        as Box<dyn Iterator<Item = &'a TypedErrorNode> + 'a>,
                    |i, b| Box::new(i.chain(b)),
                ),
            )),
            TypedExprKind::Function(FuncExpr { body, .. }) => body.errors(roots_only),
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
        match &self.kind {
            TypedExprKind::Negate(e) => e.local_identifiers(local),
            TypedExprKind::ArithOp(l, _, r) | TypedExprKind::CompareOp(l, _, r) => {
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
            TypedExprKind::Let(id, ty, e) => {
                if let Some(expr) = e {
                    expr.local_identifiers(local);
                }
                let ty = match ty {
                    None => match e {
                        None => panic!("undetermined type of local variable"),
                        Some(e) => &e.ty,
                    },
                    Some(t) => t,
                };
                match id {
                    ID::VarId(id) | ID::FuncId(id) => {
                        if local.len() <= *id {
                            local.resize(id + 1, Type::Unknown);
                        }
                        local[*id] = ty.clone();
                    }
                    ID::PubFuncId(_) => {}
                    ID::Symbol(_) => {
                        panic!("local_identifiers called on an untransformed tree")
                    }
                }
            }
            TypedExprKind::Call(op, args) => {
                op.local_identifiers(local);
                for arg in args {
                    arg.local_identifiers(local);
                }
            }
            TypedExprKind::Identifier(_) => {}
            TypedExprKind::Number(_) => {}
            TypedExprKind::Bool(_) => {}
            TypedExprKind::Function(_) => {}
            TypedExprKind::Error(_) => {}
        }
    }
}

#[derive(Debug)]
pub struct ParseResult {
    pub ast: TypedSpExpr,
    pub module_env: ModuleEnv,
}

#[cfg(test)]
mod tests {
    use crate::parser::ast::*;
    use crate::parser::*;
    use crate::span::Span;
    use crate::symbols::SymbolTable;
    use crate::types::*;

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
                end: 0,
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
            let result = parse_expr($s);
            assert!(result.is_ok(), "error: {:?}", result);
            let parse_result = parse_expr($s).unwrap();
            let error = parse_result.ast.errors(true).next();
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
            assert!(parse_expr($s).is_err())
        };
    }

    macro_rules! ast_error {
        ($s:literal) => {
            assert!(
                !parse_expr($s).unwrap().ast.errors(true).next().is_none(),
                "no errors in AST for expression: {:?}",
                $s
            )
        };
    }

    macro_rules! parses {
        ($($lhs:expr => $rhs:expr)+) => {{
            let imports = module::basis_imports();
            let mut env = LexicalEnv::new_root(&imports);
             $(
                assert_eq!(UntypedSpExpr::from($rhs).into_typed(&mut env).kind,
                           parse_expr($lhs).map(|b| b.ast.item.kind).unwrap());
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
    fn comparison_operations() {
        let one = || expr!(ExprKind::Number("1".to_string()));
        let two = || expr!(ExprKind::Number("2".to_string()));
        parses! {
            "1 == 2" => ExprKind::CompareOp(one(), CompareOp::Eq, two())
            "-1 == -2" => ExprKind::CompareOp(expr!(ExprKind::Negate(one())), CompareOp::Eq, expr!(ExprKind::Negate(two())))
        };
        // not associative
        parse_fails!("1 == 2 == 3");
    }

    #[test]
    fn identifiers() {
        // generate an empty symbol table for each test case
        let sym = || SymbolTable::default();

        parses! {
            "abc" => ExprKind::Identifier(ID::Symbol(sym().intern_str("abc")))
            "a" => ExprKind::Identifier(ID::Symbol(sym().intern_str("a")))
            "a123" => ExprKind::Identifier(ID::Symbol(sym().intern_str("a123")))
            "_" => ExprKind::Identifier(ID::Symbol(sym().intern_str("_")))
            "_a" => ExprKind::Identifier(ID::Symbol(sym().intern_str("_a")))
            "Caps" => ExprKind::Identifier(ID::Symbol(sym().intern_str("Caps")))
            "CAPS" => ExprKind::Identifier(ID::Symbol(sym().intern_str("CAPS")))
            "日本語" => ExprKind::Identifier(ID::Symbol(sym().intern_str("日本語")))
        };
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
}
