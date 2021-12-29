use crate::ast;
use crate::ast::{Expr, ExprKind, Opcode, ParseError, Type};
use crate::span::Span;
use std::fmt::Debug;
use std::ops::Range;
use thiserror::Error;
use wasmtime::ValType;

///! The compiler module ties together the lexing, parsing, ast transformation, and codegen
///! into a single abstraction. Give it source code and it gives back bytecode.

/// Compiler Errors

#[derive(Error, Debug)]
pub enum ErrorType<'a> {
    #[error("parse error: {0}")]
    ParseError(ParseError<'a>),
}

#[derive(Error, Debug)]
#[error("{error}")]
pub struct CompilerError<'a> {
    pub error: ErrorType<'a>,
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
    pub fn wasm_type(&self) -> ValType {
        match self {
            Type::Int64 => ValType::I64,
            Type::Bool => ValType::I32,
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
    /// * `file_id` - A unique number for the source file. This is intended to be a cache lookup key
    ///               and is passed to CompilerErrors for later use when printing them.
    pub fn compile(&self, program: &'a str) -> Result<ThunkSource, Vec<CompilerError<'a>>> {
        let expr = ast::parse(program).map_err(|e| self.map_parse_error(e))?;

        let mut instructions: Vec<String> = vec![];
        self.codegen(&*expr, &mut instructions);

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
            ($s:literal) => {
                instructions.push($s.to_string())
            };
            // treat multiple args as a format string with args
            ($s:literal, $($arg:tt)+) => {
                instructions.push(format!($s, $($arg)+))
            };
            ($s:expr) => {
                instructions.push($s)
            };
        }

        match &expr.kind {
            ExprKind::Error(_) => panic!("encountered an ExprKind::Error in codegen"),
            ExprKind::Number(n) => push!("i64.const {}", n),
            ExprKind::Identifier(_id) => {
                todo!()
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
                    push!("drop")
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
        }
    }

    /// Map the many ParseError types into a CompilerError
    /// with context from the original source file.
    fn map_parse_error(&self, parse_errors: Vec<ParseError<'a>>) -> Vec<CompilerError<'a>> {
        parse_errors
            .into_iter()
            .map(|parse_error| {
                let range = match parse_error {
                    ParseError::InvalidToken { location } => location..location,
                    ParseError::UnrecognizedEOF { location, .. } => location..location,
                    ParseError::UnrecognizedToken {
                        token: (l, _, r), ..
                    } => l..r,
                    ParseError::ExtraToken { token: (l, _, r) } => l..r,
                    ParseError::User {
                        error: Span { start, end, .. },
                    } => start..end,
                };
                CompilerError {
                    error: ErrorType::ParseError(parse_error),
                    span: Some(range),
                }
            })
            .collect()
    }
}
