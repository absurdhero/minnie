#[macro_use]
extern crate lalrpop_util;
#[macro_use]
extern crate log;

pub mod ast;
pub mod compiler;
pub mod error_reporting;
pub mod lexer;
pub mod runtime;
pub mod span;

lalrpop_mod!(#[allow(clippy::all)] pub grammar);
