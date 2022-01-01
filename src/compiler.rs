use std::fmt::Debug;
use std::ops::Range;

use log::Level;
use thiserror::Error;

use crate::ast;
use crate::ast::{ErrorNode, ErrorNodeKind, Expr, ExprKind, Opcode, Type, TypedSpExpr};
use crate::span::Span;

///! The compiler module ties together the lexing, parsing, ast transformation, and codegen
///! into a single abstraction. Give it source code and it gives back bytecode.

/// Compiler Errors
#[derive(Error, Debug)]
pub enum ErrorType {
    #[error("parse error: {0}")]
    ParseError(ast::AstError),
    // stores primary and secondary errors
    #[error("parse error: {0}")]
    ErrNode(ErrorNodeKind, Vec<Span<ErrorNodeKind>>),
}

#[derive(Error, Debug)]
#[error("{error}")]
pub struct CompilerError {
    pub error: ErrorType,
    pub span: Option<Range<usize>>,
}

/// An executable unit of code
pub struct ThunkSource {
    /// wasm source code in the "wat" text format
    pub wasm_text: String,
    /// The type of the return value that results from running this code
    pub return_type: Type,
}

impl Type {
    /// map data types into their wasm format
    pub fn wasm_type(&self) -> &'static str {
        match self {
            Type::Int64 => "i64",
            Type::Bool => "i32",
            Type::Void => "",
            Type::Unknown => unreachable!(),
        }
    }
}

pub struct Compiler {}

impl<'a> Compiler {
    pub fn new() -> Compiler {
        Compiler {}
    }

    /// Compiles a program in the webassembly wat format
    ///
    /// # Arguments
    ///
    /// * `program` - A string slice of the program source text
    pub fn compile(&self, program: &'a str) -> Result<ThunkSource, Vec<CompilerError>> {
        let expr = ast::parse(program).map_err(|e| self.map_parse_error(e))?;
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
        let mut instructions: Vec<String> = vec![];

        // declare locals
        expr.local_identifiers(&mut identifiers);
        for (id, ty) in identifiers.iter().enumerate() {
            instructions.push(format!("(local ${} {})", id, ty.wasm_type()))
        }

        self.codegen(&*expr, &mut instructions);

        if log_enabled!(Level::Trace) {
            trace!("instructions:\n{:?}", instructions);
        }

        let header = format!(
            r#"
            (module
              (func (export "top_level") (result {})
          "#,
            expr.ty.wasm_type()
        );

        let footer = r#"
              )
            )
        "#;

        let output = format!("{}\n{}\n{}", header, instructions.join("\n"), footer);
        Ok(ThunkSource {
            wasm_text: output,
            return_type: expr.ty,
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
            ExprKind::Identifier(id) => {
                push!("local.get ${}", id.id())
            }
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
                    if e.kind.is_expression() {
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
