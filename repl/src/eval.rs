use std::fmt;
use std::fmt::{Display, Formatter};

use minnie::ast::Type;
use thiserror::Error;
use wasmtime::*;

use minnie::compiler::ModuleSource;

///! This module executes expressions for the REPL.

pub struct Eval {
    // An engine stores and configures global compilation settings like
    // optimization level, enabled wasm features, etc.
    engine: Engine,

    // A `Store` is what owns instances, functions, globals, etc. All wasm
    // items are stored within a `Store`, and it's what we'll always be using to
    // interact with the wasm world. Custom data can be stored in stores but for
    // now we just use `()`.
    // The store is persisted between evaluation calls so that repl sessions can
    // access state across multiple lines.
    store: Store<()>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ReturnValue {
    Void,
    Integer(i64),
    Bool(bool),
}

impl Display for ReturnValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ReturnValue::Integer(i) => write!(f, "{}", i),
            ReturnValue::Bool(b) => write!(f, "{}", b),
            ReturnValue::Void => write!(f, "<void>"),
        }
    }
}

#[derive(Error, Debug)]
pub enum EvalError {
    #[error(transparent)]
    Trap(#[from] Trap),

    // wasmtime uses `anyhow` so we have to handle this error type
    #[error(transparent)]
    Any(#[from] anyhow::Error),
}

impl Eval {
    pub fn new() -> Eval {
        let engine = Engine::default();
        let store = Store::new(&engine, ());
        Eval { engine, store }
    }

    pub fn eval(&mut self, thunk_source: &ModuleSource) -> Result<ReturnValue, EvalError> {
        // Create a `Module` which represents a compiled form of our
        // input. In this case it will be JIT-compiled after
        // we parse the text returned by the compiler.
        let module = Module::new(&self.engine, &thunk_source.wasm_text)?;

        // With a compiled `Module` we can then instantiate it, creating
        // an `Instance` which represents a real running machine we can interact with.
        let instance = Instance::new(&mut self.store, &module, &[])?;

        let top_level = instance
            .get_func(&mut self.store, "top_level")
            .expect("`top_level` was not an exported function");

        if let Type::Void = thunk_source.return_type {
            let result = top_level.call(&mut self.store, &[], &mut []);
            return match result {
                Ok(_) => Ok(ReturnValue::Void),
                Err(trap) => Err(EvalError::from(trap)),
            };
        }

        let mut returns = [Val::I64(0)];
        let result = top_level.call(&mut self.store, &[], &mut returns);

        match result {
            Ok(_) => {
                let returned = &returns[0];
                match thunk_source.return_type {
                    Type::Int64 => {
                        if let Val::I64(i) = returned {
                            Ok(ReturnValue::Integer(*i))
                        } else {
                            Err(EvalError::Any(anyhow::Error::msg("type mismatch")))
                        }
                    }
                    Type::Bool => {
                        if let Val::I32(b) = returned {
                            Ok(ReturnValue::Bool(*b != 0))
                        } else {
                            Err(EvalError::Any(anyhow::Error::msg("type mismatch")))
                        }
                    }
                    Type::Void => unreachable!(),
                    Type::Unknown => unreachable!(),
                    Type::Function { .. } => todo!(),
                }
            }
            Err(trap) => Err(EvalError::from(trap)),
        }
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
        #[error("{msgs:?}")]
        Other { msgs: Vec<String> },
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
            Err(errors) => Err(TestError::Other {
                msgs: errors.into_iter().map(|e| e.to_string()).collect(),
            }),
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
    fn if_condition() {
        returns! {
            "if true {false} else {true}" => ReturnValue::Bool(false)
            "if true {1} else {2}" => ReturnValue::Integer(1)
            "if false{1} else { 2 }" => ReturnValue::Integer(2)
            "if false{ 1 } else {{2}}" => ReturnValue::Integer(2)
            "if true {1;true; 1+2} else {0;0}" => ReturnValue::Integer(3)
        }
    }

    #[test]
    fn blocks_and_sequences() {
        returns! {
            "{ if true {1} else {2} }" => ReturnValue::Integer(1)
            "{{ if true {1} else {2} }}" => ReturnValue::Integer(1)
            "2; true" => ReturnValue::Bool(true)
            "if true { if false { 2 } else { 3 } } else {0;0}" => ReturnValue::Integer(3)

            // Yielding a value despite a semicolon. Maybe not desirable.
            "true;" => ReturnValue::Bool(true)
        }
    }

    #[test]
    fn lexical_let() {
        returns! {
            "let foo = 1;" => ReturnValue::Void
            "let foo = 1; foo" => ReturnValue::Integer(1)
            "let foo = true; let bar = 2; foo" => ReturnValue::Bool(true)
            "let foo = 1; let bar = false; foo" => ReturnValue::Integer(1)
            "let foo = 1; let bar = foo; foo" => ReturnValue::Integer(1)
            "let foo = true; let bar = if foo { 1 } else { 2  }; bar " => ReturnValue::Integer(1)
            // shadowing
            "let foo = 1; let bar = { let foo = 2; foo }; foo + bar " => ReturnValue::Integer(3)
        }
    }
}
