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
                    Ok(()) => {}
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
