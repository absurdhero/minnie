extern crate pretty_env_logger;

mod eval;

use std::fs;
use std::path::Path;

use anyhow::Result;
use gumdrop::Options;
use rustyline::error::ReadlineError;

use minnie::ast::AstError;
use minnie::compiler::{Compiler, CompilerError, ErrorType};
use minnie::error_reporting;

use eval::Eval;

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

    pretty_env_logger::init();

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
        match minnie::compile_file(file) {
            Ok(bytecode) => {
                // if it compiled, evaluate it and exit if evaluation fails.
                eval.eval(&bytecode)?;
            }
            Err(_) => {
                failed = true;
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

    'outer: loop {
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

        let result = compiler.compile("repl", &input);

        match result {
            Ok(wat) => {
                prompt_level = 1;
                match eval.eval(&wat) {
                    Ok(r) => println!("{}", r),
                    Err(e) => println!("error: {}", e),
                }
            }
            Err(errors) => {
                let mut printable = vec![];
                for error in errors {
                    match error {
                        CompilerError {
                            error: ErrorType::ParseError(AstError::UnrecognizedEOF),
                            ..
                        } => {
                            prompt_level = 2;
                            continue 'outer;
                        }
                        e => {
                            prompt_level = 1;
                            printable.push(e);
                        }
                    }
                }
                error_reporting::print_error(&fake_path, &input, &printable)?;
            }
        }

        rl.add_history_entry(&input);
        input.clear();
    }
}
