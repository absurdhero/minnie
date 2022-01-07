extern crate pretty_env_logger;

use std::ffi::OsStr;
use std::fs;
use std::path::Path;

use anyhow::Result;
use gumdrop::Options;
use minnie::ast::Type;

use minnie::compiler::{Compiler, ModuleSource};
use minnie::error_reporting;

#[derive(Debug, Options)]
struct CliOptions {
    #[options(free, help = "bytecode or source file to execute")]
    file: String,

    #[options(help = "print help message")]
    help: bool,
}

/// Runs a program from bytecode or by first compiling it from source
fn main() -> Result<()> {
    let opts = CliOptions::parse_args_default_or_exit();

    pretty_env_logger::init();

    let file: String = opts.file;
    let file_path = Path::new(&file);
    let file_name = file_path
        .file_name()
        .expect("file path has no base name")
        .to_str()
        .unwrap();

    let source = fs::read_to_string(&file)?;

    // if the file is a source file, compile it first.
    let bytecode = if file_path.extension() == Some(OsStr::new("mi")) {
        let compiler = Compiler::new();
        match compiler.compile(file_name, &source) {
            Ok(bytecode) => bytecode,
            Err(errors) => {
                error_reporting::print_error(&file, &source, &errors)?;
                return Err(anyhow::Error::msg("aborting due to previous error"));
            }
        }
    } else {
        // Support bytecode files containing a single wasm function with no return value.
        // This is sufficient until top-level functions are implemented.
        ModuleSource {
            name: file_name.to_string(),
            wasm_text: source,
            return_type: Type::Void,
        }
    };

    minnie::execute(vec![bytecode])
}
