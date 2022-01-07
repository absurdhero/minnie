#[macro_use]
extern crate lalrpop_util;
#[macro_use]
extern crate log;

use crate::compiler::{Compiler, ModuleSource};
use std::path::Path;

pub mod ast;
pub mod compiler;
pub mod error_reporting;
pub mod lexer;
pub mod runtime;
pub mod span;

lalrpop_mod!(#[allow(clippy::all)] pub grammar);

/// convenience function that reads a file, compiles it, and prints any errors
pub fn compile_file(file_path: &str) -> Result<ModuleSource, anyhow::Error> {
    let path = Path::new(&file_path);
    let file_name = path
        .file_name()
        .expect("file path has no base name")
        .to_str()
        .unwrap();

    let source = std::fs::read_to_string(file_path)?;

    let compiler = Compiler::new();
    match compiler.compile(file_name, &source) {
        Ok(bytecode) => Ok(bytecode),
        Err(errors) => {
            error_reporting::print_error(file_path, &source, &errors)?;
            Err(anyhow::Error::msg("aborting due to previous error"))
        }
    }
}

/// Convenience function that executes a program.
///
/// Execution will start in the last module in the list.
pub fn execute(modules: Vec<ModuleSource>) -> Result<(), anyhow::Error> {
    let mut runtime = runtime::Runtime::new()?;

    for module in modules {
        runtime.add_module(module)?;
    }

    match runtime.eval("top_level") {
        Ok(_) => Ok(()),
        Err(err) => Err(anyhow::Error::new(err)),
    }
}
