use crate::ast;
use crate::ast::{Expr, Opcode, ParseError};
use std::error::Error;
use std::fmt;
use std::fmt::{Display, Formatter};

pub struct Compiler {}

/// Compiler Errors

#[derive(Debug)]
pub enum CompilerError<'a> {
    ParseError(ParseError<'a>),
}

impl Display for CompilerError<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CompilerError::ParseError(e) => write!(f, "parse error: {}", e),
        }
    }
}

impl Error for CompilerError<'_> {}

/// Types supported by the language
pub enum Type {
    Int64,
}

/// An executable unit of code
pub struct ThunkSource {
    /// wasm source code in the "wat" text format
    pub wasm_text: String,
    /// The type of the return value that results from running this code
    pub return_type: Type,
}

impl Compiler {
    pub fn new() -> Compiler {
        Compiler {}
    }

    /// compiles a program in the webassembly wat format
    pub fn compile<'a>(&self, program: &'a str) -> Result<ThunkSource, CompilerError<'a>> {
        let expr = ast::parse(program).map_err(CompilerError::ParseError)?;

        let mut instructions: Vec<String> = vec![];
        self.codegen(&*expr, &mut instructions);

        let header = r#"
            (module
              (func (export "top_level") (result i64)
          "#;

        let footer = r#"
              )
            )
        "#;

        let output = format!("{}\n{}\n{}", header, instructions.join("\n"), footer);
        Ok(ThunkSource {
            wasm_text: output,
            return_type: Type::Int64,
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

        match expr {
            Expr::Number(n) => push!("i64.const {}", n),
            Expr::Negate(b) => match b.as_ref() {
                Expr::Number(n) => push!("i64.const -{}", n),
                e => {
                    self.codegen(e, instructions);
                    push!("i64.const -1");
                    push!("i64.mul");
                }
            },
            Expr::Op(e1, op, e2) => {
                self.codegen(e1, instructions);
                self.codegen(e2, instructions);
                match op {
                    Opcode::Mul => push!("i64.mul"),
                    Opcode::Div => push!("i64.div_s"),
                    Opcode::Add => push!("i64.add"),
                    Opcode::Sub => push!("i64.sub"),
                };
            }
        }
    }
}
