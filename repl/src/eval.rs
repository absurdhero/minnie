use minnie::compiler::ModuleSource;
use minnie::runtime::{ReturnValue, Runtime, RuntimeError};

///! This module executes expressions for the REPL.

pub struct Eval {
    runtime: Runtime,
}

impl Eval {
    pub fn new() -> Result<Eval, anyhow::Error> {
        let runtime = Runtime::new();
        match runtime {
            Ok(runtime) => Ok(Eval { runtime }),
            Err(e) => Err(e),
        }
    }

    pub fn eval(&mut self, source: ModuleSource) -> Result<ReturnValue, RuntimeError> {
        self.runtime.add_module(source)?;
        self.runtime.eval("top_level")
    }
}

#[cfg(test)]
mod tests {
    use minnie::runtime::RuntimeError;
    use thiserror::Error;

    use crate::eval::ReturnValue;
    use crate::{eval, Compiler};

    #[derive(Error, Debug)]
    pub enum TestError {
        #[error(transparent)]
        EvalError(#[from] RuntimeError),
        #[error(transparent)]
        Any(#[from] anyhow::Error),
        #[error("{msgs:?}")]
        Other { msgs: Vec<String> },
    }

    /// takes a string of source code and executes it.
    /// Simplified error handling for tests.
    fn run(expr: &str) -> Result<ReturnValue, TestError> {
        let mut eval = eval::Eval::new()?;

        // Compile from our source language to the wasm text format (wat)
        let compiler = Compiler::new();
        let result = compiler.compile("test", expr);
        match result {
            Ok(thunk_source) => Ok(eval.eval(thunk_source)?),
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
