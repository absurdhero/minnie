mod ast;
mod compiler;
mod eval;

#[macro_use]
extern crate lalrpop_util;

lalrpop_mod!(#[allow(clippy::all)] pub grammar);

use anyhow::Result;
use gumdrop::Options;
use lalrpop_util::ParseError::UnrecognizedEOF;
use std::fs;

use crate::compiler::{Compiler, CompilerError};
use crate::eval::Eval;
use rustyline::error::ReadlineError;

#[derive(Debug, Options)]
struct CliOptions {
    #[options(free, help = "source files to evaluate")]
    files: Vec<String>,

    #[options(help = "print help message")]
    help: bool,

    #[options(help = "run interactive REPL (default unless files are specified)")]
    interactive: bool,
}

/// Parses arguments and either executes a file or presents an interactive prompt
fn main() -> Result<()> {
    let opts = CliOptions::parse_args_default_or_exit();

    let files: Vec<String> = opts.files;
    let mut interactive: bool = opts.interactive;
    if files.is_empty() {
        interactive = true;
    }

    let mut eval = eval::Eval::new();

    for file in files {
        let contents = fs::read_to_string(file)?;
        // Compile from our source language to the wasm text format (wat)
        let compiler = Compiler::new();
        let result = compiler.compile(&contents);
        match result {
            Ok(wat) => {
                if let Err(e) = eval.eval(&wat) {
                    println!("error: {:?}", e);
                    std::process::exit(1)
                }
            }
            Err(e) => {
                println!("{}", e);
                panic!();
            }
        }
    }

    if interactive {
        let compiler = Compiler::new();
        repl(&compiler, &mut eval)
    } else {
        Ok(())
    }
}

/// reads a line of input, evaluates it, prints the result,
/// and loops until the user exits.
fn repl(compiler: &Compiler, eval: &mut Eval) -> Result<()> {
    let mut input: String = String::with_capacity(1024);

    let mut prompt_level = 1;
    let mut rl = rustyline::Editor::<()>::new();

    loop {
        let prompt = if prompt_level == 1 { "> " } else { "# " };

        let readline = rl.readline(prompt);
        match readline {
            Ok(line) => input.push_str(line.as_str()),
            Err(ReadlineError::Interrupted) => std::process::exit(1),
            Err(ReadlineError::Eof) => std::process::exit(1),
            Err(err) => {
                println!("error: {:?}", err);
                std::process::exit(1)
            }
        }

        match compiler.compile(input.as_ref()) {
            Ok(wat) => {
                prompt_level = 1;
                match eval.eval(&wat) {
                    Ok(r) => println!("{}", r),
                    Err(e) => println!("error: {:?}", e),
                }
            }
            Err(CompilerError::ParseError(UnrecognizedEOF {
                expected: _,
                location: _,
            })) => {
                prompt_level = 2;
                continue;
            }
            Err(e) => {
                prompt_level = 1;
                println!("error: compiler: {:?}", e);
            }
        }

        input.clear();
    }
}

#[cfg(test)]
mod tests {
    use crate::eval::{EvalError, ReturnValue};
    use crate::{eval, Compiler};
    use thiserror::Error;

    #[derive(Error, Debug)]
    pub enum TestError {
        #[error(transparent)]
        EvalError(#[from] EvalError),
        #[error(transparent)]
        Any(#[from] anyhow::Error),
        #[error("{msg}")]
        Other { msg: String },
    }

    /// takes a string of source code and executes it.
    /// Simplified error handling for tests.
    fn run(expr: &str) -> Result<ReturnValue, TestError> {
        let mut eval = eval::Eval::new();

        // Compile from our source language to the wasm text format (wat)
        let compiler = Compiler::new();
        let result = compiler.compile(&expr);
        match result {
            Ok(thunk_source) => Ok(eval.eval(&thunk_source)?),
            Err(e) => Err(TestError::Other { msg: e.to_string() }),
        }
    }

    #[test]
    fn numeric_operations() {
        assert_eq!(run("22").unwrap(), ReturnValue::Integer(22));
        assert_eq!(run("(22)").unwrap(), ReturnValue::Integer(22));
        assert_eq!(run("((22))").unwrap(), ReturnValue::Integer(22));
        assert!(run("((22)").is_err());

        assert_eq!(run("1+2").unwrap(), ReturnValue::Integer(3));
        assert_eq!(run("1-2").unwrap(), ReturnValue::Integer(-1));
        assert_eq!(run("2 * 3").unwrap(), ReturnValue::Integer(6));
        assert_eq!(run("10 / 2").unwrap(), ReturnValue::Integer(5));
        assert_eq!(run("11 / 2").unwrap(), ReturnValue::Integer(5));
        assert_eq!(run("1 + 2 * 3").unwrap(), ReturnValue::Integer(7));

        // unary minus
        assert_eq!(run("-2").unwrap(), ReturnValue::Integer(-2));
        assert_eq!(run("4 * -2").unwrap(), ReturnValue::Integer(-8));
        assert_eq!(run("4*-2").unwrap(), ReturnValue::Integer(-8));
        assert_eq!(run("-(1+2)").unwrap(), ReturnValue::Integer(-3));
        assert_eq!(run("-(-(-1))").unwrap(), ReturnValue::Integer(-1));
        assert_eq!(run("7--2").unwrap(), ReturnValue::Integer(9));
    }
}
