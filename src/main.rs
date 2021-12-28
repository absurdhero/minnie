#[macro_use]
extern crate lalrpop_util;

use std::fs;

use anyhow::Result;
use gumdrop::Options;
use lalrpop_util::ParseError::UnrecognizedEOF;
use rustyline::error::ReadlineError;

use crate::compiler::{Compiler, CompilerError, ErrorType};
use crate::eval::Eval;

mod ast;
mod compiler;
mod error_reporting;
mod eval;
mod span;

lalrpop_mod!(#[allow(clippy::all)] pub grammar);

#[derive(Debug, Options)]
struct CliOptions {
    #[options(free, help = "source files to compile and execute")]
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

    // keep the same environment state by using the same evaluator for files and the repl
    let mut eval = eval::Eval::new();
    let mut failed = false;

    for file in &files {
        // Compile from our source language to the wasm text format (wat)
        let compiler = Compiler::new();
        let source = fs::read_to_string(file)?;

        match compiler.compile(&source) {
            Ok(bytecode) => {
                // if it compiled, evaluate it and exit if evaluation fails.
                eval.eval(&bytecode)?;
            }
            Err(e) => {
                failed = true;
                error_reporting::print_error(file, &source, e)?;
            }
        }
    }

    if failed {
        Err(anyhow::Error::msg("aborting due to previous error"))
    } else if interactive {
        let compiler = Compiler::new();
        repl(compiler, &mut eval)
    } else {
        Ok(())
    }
}

/// reads a line of input, evaluates it, prints the result,
/// and loops until the user exits.
fn repl(compiler: Compiler, eval: &mut Eval) -> Result<()> {
    let mut input: String = String::with_capacity(1024);

    let mut expression_counter = 1;
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
                println!("error: {}", err);
                std::process::exit(1)
            }
        }

        let fake_path = format!("REPL#{}", expression_counter);
        expression_counter += 1;

        let result = compiler.compile(&input);

        match result {
            Ok(wat) => {
                prompt_level = 1;
                match eval.eval(&wat) {
                    Ok(r) => println!("{}", r),
                    Err(e) => println!("error: {}", e),
                }
            }
            Err(CompilerError {
                error: ErrorType::ParseError(UnrecognizedEOF { .. }),
                ..
            }) => {
                prompt_level = 2;
                continue;
            }
            Err(error) => {
                prompt_level = 1;
                error_reporting::print_error(&fake_path, &input, error)?;
            }
        }

        rl.add_history_entry(&input);
        input.clear();
    }
}

#[cfg(test)]
mod tests {
    use thiserror::Error;

    use crate::eval::{EvalError, ReturnValue};
    use crate::{eval, Compiler};

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
        let result = compiler.compile(expr);
        match result {
            Ok(thunk_source) => Ok(eval.eval(&thunk_source)?),
            Err(e) => Err(TestError::Other { msg: e.to_string() }),
        }
    }

    macro_rules! returns {
        ($($lhs:expr => $rhs:expr)+) => {{
             $(
                assert_eq!(run($lhs).unwrap(), $rhs);
             )+
        }};
    }

    #[test]
    fn numeric_operations() {
        returns! {
            "22" => ReturnValue::Integer(22)
            "(22)" => ReturnValue::Integer(22)
            "((1))" => ReturnValue::Integer(1)
        }
        assert!(run("((22)").is_err());

        returns! {
            "1+2" => ReturnValue::Integer(3)
            "1-2" => ReturnValue::Integer(-1)
            "2 * 3" => ReturnValue::Integer(6)
            "10 / 2" => ReturnValue::Integer(5)
            "11 / 2" => ReturnValue::Integer(5)
            "1 + 2 * 3" => ReturnValue::Integer(7)
        }

        // unary minus
        returns! {
            "-2" => ReturnValue::Integer(-2)
            "4 * -2" => ReturnValue::Integer(-8)
            "4*-2" => ReturnValue::Integer(-8)
            "-(1+2)" => ReturnValue::Integer(-3)
            "-(-(-1))" => ReturnValue::Integer(-1)
            "7--2" => ReturnValue::Integer(9)
        }
    }

    #[test]
    fn boolean() {
        returns! {
            "if true {false} else {true}" => ReturnValue::Bool(false)
            "if false{1} else { 2 }" => ReturnValue::Integer(2)
            "if true {1;true; 1+2} else {0;0}" => ReturnValue::Integer(3)
        }
    }

    #[test]
    fn if_condition() {
        returns! {
            "if true {1} else {2}" => ReturnValue::Integer(1)
            "if false{1} else { 2 }" => ReturnValue::Integer(2)
            "if true {1;true; 1+2} else {0;0}" => ReturnValue::Integer(3)
        }
    }
}
