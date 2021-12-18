mod compiler;
mod eval;

use anyhow::Result;
use gumdrop::Options;
use std::fs;

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

    let mut eval = eval::Eval::new()?;

    for file in files {
        let contents = fs::read_to_string(file)?;
        if let Err(e) = eval.eval(&contents) {
            println!("error: {:?}", e);
            std::process::exit(1)
        }
    }

    if interactive {
        repl(&mut eval)
    } else {
        Ok(())
    }
}

fn repl(eval: &mut Eval) -> Result<()> {
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

        match eval_line(&mut rl, eval, input.as_ref()) {
            Ok(true) => prompt_level = 1,
            Ok(false) => {
                prompt_level = 2;
                continue;
            }
            Err(e) => {
                prompt_level = 1;
                println!("error: {:?}", e)
            }
        }
        input.clear();
    }
}

/// Parses and runs a command.
/// Returns false if the input is incomplete.
fn eval_line(rl: &mut rustyline::Editor<()>, eval: &mut eval::Eval, input: &str) -> Result<bool> {
    let result = eval.eval(input).map(|_| true);

    // add every line to the history for now.
    // This will change once incomplete expressions are possible.
    rl.add_history_entry(input);

    result
}
