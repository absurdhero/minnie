use std::fmt::Debug;
use std::ops::Range;

use log::Level;
use thiserror::Error;

use crate::ast;
use crate::ast::ExprKind::Identifier;
use crate::ast::{ErrorNode, ErrorNodeKind, Expr, ExprKind, Opcode, ParseResult, TypedSpExpr};
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
    /// The type of the return value that results from running this code
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
            Type::Unknown => unreachable!(),
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
        let ParseResult {
            ast: expr,
            module_env,
        } = ast::parse(program).map_err(|e| self.map_parse_error(e))?;
        let ast_errors: Vec<CompilerError> = expr
            .errors(true)
            .into_iter()
            .map(|n| match n {
                ErrorNode::<TypedSpExpr> {
                    kind: top_err,
                    expr: Some(top_expr),
                } => {
                    let child_errors = top_expr
                        .errors(false)
                        .map(|err_node| match &err_node.expr {
                            None => (expr.start..expr.end, err_node.kind.clone()).into(),
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

        if log_enabled!(Level::Trace) {
            trace!("ast:\n{:#?}\n", expr.item.kind);
        }

        let mut identifiers = vec![];
        let mut import_decls: Vec<String> = vec![];
        let mut instructions: Vec<String> = vec![];

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

        // declare locals
        expr.local_identifiers(&mut identifiers);
        for (id, ty) in identifiers.iter().enumerate() {
            let type_descriptor = match ty {
                // the funcref type is i32. Maybe we need Type::FuncRef?
                Type::Function { .. } => "i32".to_string(),
                _ => ty.wasm_type(),
            };
            instructions.push(format!("(local ${} {})", id, type_descriptor))
        }

        // generate table of function references for all imports and
        // functions defined in this module.
        let funcrefs = format!(
            "(table {} funcref)\n  (elem (i32.const 0) {})",
            import_decls.len(),
            (0..(import_decls.len()))
                .into_iter()
                .map(|n| format!("${}", n.to_string()))
                .collect::<Vec<_>>()
                .join(" "),
        );

        self.codegen(&*expr, &mut instructions);

        trace!("instructions:\n{:?}", instructions);

        let output = format!(
            r#"
(module
  ;; imports
  {}
  ;; funcref table
  {}
  ;; function declarations
  (func (export "top_level") (result {})
    {}
  )
)
"#,
            import_decls.join("\n  "),
            funcrefs,
            expr.ty.wasm_type(),
            instructions.join("\n    "),
        );
        Ok(ModuleSource {
            name: file_name.to_string(),
            wasm_text: output,
            return_type: expr.ty.clone(),
        })
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
                ID::VarId(_) => push!("local.get ${}", id.id()),
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
                push!("local.set ${}", id.id());
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
