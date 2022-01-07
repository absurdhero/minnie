extern crate pretty_env_logger;

use std::fs;
use std::path::{Path, PathBuf};

use anyhow::Result;
use gumdrop::Options;

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

    let out: Option<String> = opts.output;
    let output = out
        .map(PathBuf::from)
        .unwrap_or_else(|| file_path.with_extension("minw"));

    let bytecode = minnie::compile_file(&file)?;

    // if it compiled, write it to disk.
    match fs::write(output, bytecode.wasm_text) {
        Ok(_) => Ok(()),
        Err(_) => Err(anyhow::Error::msg("could not write output file")),
    }
}
