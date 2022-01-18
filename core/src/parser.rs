use self::ast::{AstError, ErrorRecovery, ParseError, ParseResult, UntypedSpExpr};
use self::lalrpop_support::map_lalrpop_error;
use crate::lexer::Lexer;
use crate::module::ModuleEnv;
use crate::parser::ast::{ExprKind, FuncExpr, TypedSpExpr};
use crate::parser::lexical_env::LexicalEnv;
use crate::span::Span;
use crate::types::{Type, ID};
use crate::{grammar, module};

pub mod ast;
pub(super) mod lalrpop_support;

mod lexical_env;

/// Parse program text and return its type-checked AST
///
/// # arguments
///
/// * `program` - The program text for a single module
pub fn parse_module(program: &str) -> Result<Module, Vec<Span<AstError>>> {
    let mut lexer = Lexer::new(program);
    let mut recovered_errors: Vec<ErrorRecovery<'_>> = Vec::new();

    let parser = grammar::ProgramParser::new();
    let result: Result<UntypedSpExpr, ParseError> = parser.parse(&mut recovered_errors, &mut lexer);

    validate(lexer, recovered_errors, result).map(Module::from)
}

/// Parse an expression and return its type-checked AST
///
/// # arguments
///
/// * `expr` - The text of an expression
pub fn parse_expr(expr_str: &str) -> Result<ParseResult, Vec<Span<AstError>>> {
    let mut lexer = Lexer::new(expr_str);
    let mut recovered_errors: Vec<ErrorRecovery<'_>> = Vec::new();

    let parser = grammar::ReplExpressionParser::new();
    let result: Result<UntypedSpExpr, ParseError> = parser.parse(&mut recovered_errors, &mut lexer);

    validate(lexer, recovered_errors, result)
}

/// Parse an expression and wrap it in a top-level function.
///
/// # arguments
///
/// * `expr` - The text of an expression
pub fn parse_expr_as_top_level(str_expr: &str) -> Result<Module, Vec<Span<AstError>>> {
    let result = parse_expr(str_expr);
    result.map(|ParseResult { ast, module_env }| {
        let range = ast.range();
        let ty = ast.ty.clone();
        let wrapper = ExprKind::Function(FuncExpr {
            name: "main".to_string(),
            id: ID::PubFuncId("main".to_string()),
            params: vec![],
            returns: ty.clone(),
            body: ast,
        });
        let wrapper = TypedSpExpr::new(
            range.start,
            range.end,
            wrapper,
            Type::Function {
                params: vec![],
                returns: Box::new(ty),
            },
        );
        Module {
            functions: vec![wrapper],
            module_env,
        }
    })
}

pub struct Module {
    /// Top level functions
    pub functions: Vec<TypedSpExpr>,
    pub module_env: ModuleEnv,
}

impl From<ParseResult> for Module {
    fn from(result: ParseResult) -> Self {
        let ParseResult { ast, module_env } = result;
        if let ExprKind::Block(exprs) = ast.item.kind {
            Module {
                // Currently, only functions exist at the top-level.
                functions: exprs,
                module_env,
            }
        } else {
            panic!("root of ast is not a block");
        }
    }
}

fn validate(
    lexer: Lexer,
    recovered_errors: Vec<ErrorRecovery>,
    result: Result<UntypedSpExpr, ParseError>,
) -> Result<ParseResult, Vec<Span<AstError>>> {
    // convert lex errors into AstError
    let mut errors: Vec<Span<AstError>> = lexer
        .errors
        .into_iter()
        // map lex errors into AstError
        .map(|s| s.map(AstError::LexError))
        // append any errors encountered during parsing
        .chain(
            recovered_errors
                .into_iter()
                .map(|r| map_lalrpop_error(&r.error)),
        )
        .collect();

    match result {
        Ok(expr) => {
            // do type checking only if there are no parse errors
            if errors.is_empty() {
                let module_env = module::basis_imports();
                let mut env = LexicalEnv::new_root(&module_env);
                let typed_tree = expr.into_typed(&mut env);
                Ok(ParseResult {
                    ast: typed_tree,
                    module_env,
                })
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
