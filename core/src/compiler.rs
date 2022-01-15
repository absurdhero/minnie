use std::fmt::Debug;
use std::ops::Range;

use thiserror::Error;

use crate::ast;
use crate::ast::ExprKind::Identifier;
use crate::ast::{
    ErrorNode, ErrorNodeKind, Expr, ExprKind, FuncExpr, Opcode, TypedExprKind, TypedSpExpr,
};
use crate::span::Span;
use crate::types::{Type, ID};

///! The compiler module ties together the lexing, parsing, ast transformation, and codegen
///! into a single abstraction. Give it source code and it gives back bytecode.

/// Compiler Errors
#[derive(Error, Debug)]
pub enum ErrorType {
    #[error("parse error: {0}")]
    ParseError(ast::AstError),
    // stores primary and secondary errors
    #[error("error: {0}")]
    ErrNode(ErrorNodeKind, Vec<Span<ErrorNodeKind>>),
}

/// Errors caused by a fault in the program being compiled
#[derive(Error, Debug)]
#[error("{error}")]
pub struct CompilerError {
    pub error: ErrorType,
    pub span: Option<Range<usize>>,
}

/// An executable unit of code
#[derive(Debug)]
pub struct ModuleSource {
    /// name of the module. Usually derived from the file name.
    pub name: String,
    /// wasm source code in the "wat" text format
    pub wasm_text: String,
    /// The return value of the `main` function
    pub return_type: Type,
}

impl Type {
    /// map data types into their wasm format
    pub fn wasm_type(&self) -> String {
        match self {
            Type::Int64 => "i64".to_string(),
            Type::Bool => "i32".to_string(),
            Type::Void => "".to_string(),
            Type::Function { params, returns } => {
                // This does not do the right thing if a type parameter is itself a function.
                // But we don't support first class functions yet anyway.
                let mut out = String::new();
                for param in params {
                    out.push_str(format!(" (param {})", param.wasm_type()).as_str());
                }
                if returns.as_ref() != &Type::Void {
                    out.push_str(format!(" (result {})", returns.wasm_type()).as_str());
                }
                out
            }
            Type::Unknown => unreachable!("attempted to get wasm type for unknown type"),
        }
    }
}

pub struct Compiler {}

impl<'a> Compiler {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Compiler {
        Compiler {}
    }

    /// Compiles a program in the webassembly wat format
    ///
    /// # Arguments
    ///
    /// * `file_name` - The base name of the file (without extension)
    /// * `program` - A string slice of the program source text
    pub fn compile(
        &self,
        file_name: &str,
        program: &'a str,
    ) -> Result<ModuleSource, Vec<CompilerError>> {
        self.compile_ast(
            file_name,
            ast::parse_module(program).map_err(|e| self.map_parse_error(e))?,
        )
    }

    /// Compiles a single expression as a webassembly function
    ///
    /// # Arguments
    ///
    /// * `file_name` - The base name of the file (without extension)
    /// * `text` - An expression in text form
    pub fn compile_expression(
        &self,
        file_name: &str,
        text: &'a str,
    ) -> Result<ModuleSource, Vec<CompilerError>> {
        let parse_result =
            ast::parse_expr_as_top_level(text).map_err(|e| self.map_parse_error(e))?;

        self.compile_ast(file_name, parse_result)
    }

    /// Compiles a parsed AST
    ///
    /// # Arguments
    ///
    /// * `file_name` - The base name of the file (without extension)
    /// * `parse_result` - A successfully parsed AST
    fn compile_ast(
        &self,
        file_name: &str,
        module: ast::Module,
    ) -> Result<ModuleSource, Vec<CompilerError>> {
        let ast::Module {
            functions: exprs,
            module_env,
        } = module;
        let ast_errors: Vec<CompilerError> = exprs
            .iter()
            .map(|e| e.errors(true))
            .flatten()
            .into_iter()
            .map(|n| match n {
                ErrorNode::<TypedSpExpr> {
                    kind: top_err,
                    expr: Some(top_expr),
                } => {
                    let child_errors = top_expr
                        .errors(false)
                        .map(|err_node| match &err_node.expr {
                            None => (top_expr.start..top_expr.end, err_node.kind.clone()).into(),
                            Some(e) => (Range::<usize>::from(e), err_node.kind.clone()).into(),
                        })
                        .collect();
                    CompilerError {
                        error: ErrorType::ErrNode(top_err.clone(), child_errors),
                        span: n.expr.as_ref().map(|n| n.into()),
                    }
                }
                ErrorNode {
                    kind: top_err,
                    expr: None,
                } => CompilerError {
                    error: ErrorType::ErrNode(top_err.clone(), vec![]),
                    span: n.expr.as_ref().map(|n| n.into()),
                },
            })
            .collect();
        if !ast_errors.is_empty() {
            return Err(ast_errors);
        }

        trace!("ast:\n{:#?}\n", exprs);

        let mut import_decls: Vec<String> = vec![];
        let mut function_definitions: Vec<String> = vec![];

        // declare imports
        for (index, (name, ty)) in module_env.imports.iter().enumerate() {
            let namespace = "base";
            import_decls.push(format!(
                "(import \"{}\" \"{}\" (func ${} {}))",
                namespace,
                name,
                index,
                ty.wasm_type()
            ))
        }

        let mut main_func: Option<&FuncExpr<TypedSpExpr>> = None;
        for expr in exprs.iter() {
            match &expr.kind {
                TypedExprKind::Function(func) => {
                    if &func.name == "main" {
                        main_func = Some(func);
                    }
                    function_definitions.push(self.function_def(func, &expr.ty))
                }
                _ => {
                    panic!("only functions can exist at the top level")
                }
            }
        }

        // generate table of function references for all imports and
        // functions defined in this module.
        let total_funcs = import_decls.len() + exprs.len();
        let funcrefs = format!(
            "(table {} funcref)\n  (elem (i32.const 0) {} {})",
            total_funcs,
            (0..(import_decls.len()))
                .into_iter()
                .map(|n| format!("${}", n))
                .collect::<Vec<_>>()
                .join(" "),
            exprs
                .iter()
                .filter_map(|e| {
                    match &e.kind {
                        TypedExprKind::Function(f) => Some(format!("${}", &f.id)),
                        _ => None,
                    }
                })
                .collect::<Vec<String>>()
                .join(" ")
        );

        let output = format!(
            r#"
(module
  ;; imports
  {}
  ;; funcref table
  {}
  ;; function declarations
  {}
)
"#,
            import_decls.join("\n  "),
            funcrefs,
            function_definitions.join("\n  "),
        );

        Ok(ModuleSource {
            name: file_name.to_string(),
            wasm_text: output,
            return_type: main_func.map_or(Type::Void, |f| f.body.ty.clone()),
        })
    }

    fn function_def(&self, func: &FuncExpr<TypedSpExpr>, func_ty: &Type) -> String {
        let mut instructions: Vec<String> = vec![];
        let mut identifiers = vec![];

        // declare locals
        func.body.local_identifiers(&mut identifiers);
        for (id, ty) in identifiers.iter().enumerate() {
            // unknown types represent gaps in the local index space
            if ty == &Type::Unknown {
                continue;
            }
            let type_descriptor = match ty {
                // the funcref type is i32. Maybe we need Type::FuncRef?
                Type::Function { .. } => "i32".to_string(),
                _ => ty.wasm_type(),
            };
            instructions.push(format!("(local ${} {})", id, type_descriptor))
        }

        self.codegen(&*func.body, &mut instructions);

        trace!("instructions:\n{:?}", instructions);
        format!(
            r#"
  (func ${} {}
    {}
  ){}
"#,
            func.id,
            func_ty.wasm_type(),
            instructions.join("\n    "),
            // export public functions
            if let ID::PubFuncId(name) = &func.id {
                format!(r#"(export "{0}" (func ${0}))"#, name)
            } else {
                "".to_string()
            }
        )
    }

    fn codegen(&self, expr: &Expr, instructions: &mut Vec<String>) {
        macro_rules! push {
            // convert literals into String
            // e.g: `push!("literal instruction")`
            ($s:literal) => {
                instructions.push($s.to_string())
            };
            // treat multiple args as a format string with args
            // e.g: `push!("formatted {}", substitution)`
            ($s:literal, $($arg:tt)+) => {
                instructions.push(format!($s, $($arg)+))
            };
            ($s:expr) => {
                instructions.push($s)
            };
        }

        match &expr.kind {
            ExprKind::Error(ErrorNode { kind: _, expr: _ }) => {
                panic!("encountered an ErrorNode in codegen")
            }
            ExprKind::Number(n) => push!("i64.const {}", n),
            ExprKind::Identifier(id) => match id {
                ID::Name(_) => unreachable!(),
                ID::PubFuncId(_) => push!("i32.const ${}", id.name()),
                ID::VarId(_) => push!("local.get {}", id.id()),
                ID::FuncId(_) => push!("i32.const {}", id.id()),
            },
            ExprKind::Negate(b) => match b.as_ref() {
                Expr {
                    kind: ExprKind::Number(n),
                    ty: Type::Int64,
                } => push!("i64.const -{}", n),
                e => {
                    self.codegen(e, instructions);
                    push!("i64.const -1");
                    push!("i64.mul");
                }
            },
            ExprKind::Equal(l, r) => {
                self.codegen(l, instructions);
                self.codegen(r, instructions);
                match l.ty {
                    Type::Int64 => push!("i64.eq"),
                    Type::Bool => push!("i32.eq"),
                    Type::Void => push!("i32.const 0"),
                    Type::Function { .. } => push!("i32.eq"),
                    Type::Unknown => panic!("unknown type during codegen"),
                }
            }
            ExprKind::Call(op, params) => {
                for param in params {
                    self.codegen(param, instructions);
                }
                if let Identifier(ID::FuncId(id)) = op.kind {
                    // direct call when the function ID is known at compile time
                    push!("call ${}", id);
                } else {
                    // otherwise, evaluate the operator which will push a function reference
                    // onto the stack where call_indirect will read it.
                    self.codegen(op, instructions);
                    push!("call_indirect {}", op.ty.wasm_type())
                }
            }
            ExprKind::Function(_) => {
                // Inner functions need to be lifted. They shouldn't be nested in the AST.
                panic!("function found inside another function")
            }
            ExprKind::Op(e1, op, e2) => {
                self.codegen(e1, instructions);
                self.codegen(e2, instructions);
                match op {
                    Opcode::Mul => push!("i64.mul"),
                    Opcode::Div => push!("i64.div_s"),
                    Opcode::Add => push!("i64.add"),
                    Opcode::Sub => push!("i64.sub"),
                };
            }
            ExprKind::Block(v) => {
                // execute and throw out the result of every expr but the last
                for e in &v[0..(v.len() - 1)] {
                    self.codegen(e, instructions);
                    if e.kind.is_expression() && e.ty != Type::Void {
                        push!("drop")
                    }
                }
                self.codegen(&v[v.len() - 1], instructions);
            }
            ExprKind::If(cond, t, f) => {
                self.codegen(cond, instructions);
                push!("if (result {})", t.ty.wasm_type());
                self.codegen(t, instructions);
                push!("else");
                self.codegen(f, instructions);
                push!("end");
            }
            ExprKind::Bool(true) => {
                push!("i32.const 1")
            }
            ExprKind::Bool(false) => {
                push!("i32.const 0")
            }
            ExprKind::Let(id, _t, e) => {
                if let Some(e) = e {
                    self.codegen(e, instructions);
                }
                push!("local.set {}", id.id());
            }
        }
    }

    /// Map from Span<AstError> into a CompilerError
    /// with context from the original source file.
    fn map_parse_error(&self, parse_errors: Vec<Span<ast::AstError>>) -> Vec<CompilerError> {
        parse_errors
            .into_iter()
            .map(|parse_error| {
                let Span {
                    start,
                    end,
                    item: error,
                } = parse_error;
                CompilerError {
                    error: ErrorType::ParseError(error),
                    span: Some(start..end),
                }
            })
            .collect()
    }
}
