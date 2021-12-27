use crate::ast;
use crate::ast::{Expr, ExprKind, Opcode, ParseError, Type};
use crate::span::Span;
use std::fmt;
use std::fmt::Formatter;
use thiserror::Error;
use wasmtime::ValType;

pub struct Compiler {}

/// Compiler Errors

#[derive(Error, Debug)]
pub enum ErrorType<'a> {
    #[error("parse error: {0}")]
    ParseError(ParseError<'a>),
}

#[derive(Error, Debug)]
pub struct CompilerError<'a> {
    pub error: ErrorType<'a>,
    pub excerpt: Option<Span<&'a str>>,
}

impl fmt::Display for CompilerError<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(e) = &self.excerpt {
            write!(f, "{} at \"{}\" ", self.error, **e)
        } else {
            write!(f, "{}", self.error)
        }
    }
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

impl Compiler {
    pub fn new() -> Compiler {
        Compiler {}
    }

    /// compiles a program in the webassembly wat format
    pub fn compile<'a>(&self, program: &'a str) -> Result<ThunkSource, CompilerError<'a>> {
        let expr = ast::parse(program).map_err(|e| map_parse_error(e, program))?;

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
            ExprKind::Number(n) => push!("i64.const {}", n),
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
            ExprKind::Sequence(v) => {
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
}

/// Map the many ParseError types into a CompilerError
/// with context from the original source code.
fn map_parse_error<'a>(parse_error: ParseError<'a>, program: &'a str) -> CompilerError<'a> {
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
        excerpt: Some((range.clone(), &program[range]).into()),
    }
}
