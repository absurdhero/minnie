use self::ast::{AstError, ErrorRecovery, ParseError, ParseResult, UntypedSpExpr};
use self::lalrpop_support::map_lalrpop_error;
use crate::lexer::Lexer;
use crate::module::ModuleEnv;
use crate::parser::ast::{ExprKind, FuncExpr, ModExpr, TypedSpExpr};
use crate::parser::lexical_env::LexicalEnv;
use crate::span::Span;
use crate::symbols::SymbolTable;
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
    let mut symbols = SymbolTable::default();

    let parser = grammar::ProgramParser::new();
    let result: Result<ModExpr<UntypedSpExpr>, ParseError> =
        parser.parse(&mut recovered_errors, &mut symbols, &mut lexer);

    let mut errors = collect_errors(lexer, recovered_errors);

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
    .map(Module::from)
}

/// Parse an expression and return its type-checked AST
///
/// # arguments
///
/// * `expr` - The text of an expression
pub fn parse_expr(expr_str: &str) -> Result<ParseResult, Vec<Span<AstError>>> {
    let mut symbols = SymbolTable::default();
    parse_expr_inner(expr_str, &mut symbols)
}

/// Same as `parse_expr` but has the symbol table as an out parameter
/// so further parsing or AST manipulation can occur later
fn parse_expr_inner(
    expr_str: &str,
    symbols: &mut SymbolTable,
) -> Result<ParseResult, Vec<Span<AstError>>> {
    let mut lexer = Lexer::new(expr_str);
    let mut recovered_errors: Vec<ErrorRecovery<'_>> = Vec::new();

    let parser = grammar::ReplExpressionParser::new();
    let result: Result<UntypedSpExpr, ParseError> =
        parser.parse(&mut recovered_errors, symbols, &mut lexer);

    let mut errors = collect_errors(lexer, recovered_errors);

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

/// Parse an expression and wrap it in a top-level function.
///
/// # arguments
///
/// * `expr` - The text of an expression
pub fn parse_expr_as_top_level(str_expr: &str) -> Result<Module, Vec<Span<AstError>>> {
    let mut symbols = SymbolTable::default();
    let result = parse_expr_inner(str_expr, &mut symbols);
    result.map(|ParseResult { ast, module_env }| {
        let range = ast.range();
        let ty = ast.ty.clone();
        let wrapper = ExprKind::Function(FuncExpr {
            name: symbols.intern_str("main"),
            id: ID::PubFuncId(symbols.intern_str("main")),
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
    result: Result<ModExpr<UntypedSpExpr>, ParseError>,
) -> Result<ParseResult, Vec<Span<AstError>>> {
    let mut errors = collect_errors(lexer, recovered_errors);

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

/// Convert lex errors and lalrpop ParserError into AstError
fn collect_errors(lexer: Lexer, recovered_errors: Vec<ErrorRecovery>) -> Vec<Span<AstError>> {
    lexer
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
        .collect()
}
