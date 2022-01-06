extern crate pretty_env_logger;

use std::ffi::OsStr;
use std::fs;
use std::path::Path;

use anyhow::Result;
use gumdrop::Options;
use minnie::ast::Type;

use minnie::compiler::{Compiler, ThunkSource};
use minnie::error_reporting;
use minnie::eval;

#[derive(Debug, Options)]
struct CliOptions {
    #[options(free, help = "bytecode or source file to execute")]
    file: String,

    #[options(help = "print help message")]
    help: bool,
}

/// Parses arguments and either executes a file or presents an interactive prompt
fn main() -> Result<()> {
    let opts = CliOptions::parse_args_default_or_exit();

    pretty_env_logger::init();

    let file: String = opts.file;
    let file_path = Path::new(&file);

    let source = fs::read_to_string(&file)?;

    // if the file is a source file, compile it first.
    let bytecode = if file_path.extension() == Some(OsStr::new("mi")) {
        let compiler = Compiler::new();
        match compiler.compile(&source) {
            Ok(bytecode) => bytecode,
            Err(errors) => {
                error_reporting::print_error(&file, &source, &errors)?;
                return Err(anyhow::Error::msg("aborting due to previous error"));
            }
        }
    } else {
        // Support bytecode files containing a single wasm function with no return value.
        // This is sufficient until top-level functions are implemented.
        ThunkSource {
            wasm_text: source,
            return_type: Type::Void,
        }
    };

    let mut eval = eval::Eval::new();
    match eval.eval(&bytecode) {
        Ok(_) => Ok(()),
        Err(err) => Err(anyhow::Error::new(err)),
    }
}
