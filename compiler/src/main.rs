extern crate pretty_env_logger;

use std::fs;
use std::path::{Path, PathBuf};

use anyhow::Result;
use gumdrop::Options;

use minnie::compiler::Compiler;
use minnie::error_reporting;

#[derive(Debug, Options)]
struct CliOptions {
    #[options(free, help = "source file")]
    file: String,

    #[options(help = "name of the compiled file (default: input name with .minw extension")]
    output: Option<String>,

    #[options(help = "print help message")]
    help: bool,
}

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

    // Compile from our source language to the wasm text format (wat)
    let compiler = Compiler::new();
    let source = fs::read_to_string(&file)?;
    let out: Option<String> = opts.output;
    let output = out
        .map(|s| PathBuf::from(s))
        .unwrap_or(file_path.with_extension("minw"));

    match compiler.compile(&file_name, &source) {
        Ok(bytecode) => {
            // if it compiled, write it to disk.
            match fs::write(output, bytecode.wasm_text) {
                Ok(_) => Ok(()),
                Err(_) => Err(anyhow::Error::msg("could not write output file")),
            }
        }
        Err(errors) => {
            error_reporting::print_error(&file, &source, &errors)?;
            Err(anyhow::Error::msg("aborting due to previous error"))
        }
    }
}
