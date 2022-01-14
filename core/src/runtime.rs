use std::fmt;
use std::fmt::{Display, Formatter};

use crate::module;
use crate::types::Type;
use thiserror::Error;
use wasmtime::*;
use wasmtime_wasi::{WasiCtx, WasiCtxBuilder};

use crate::compiler::ModuleSource;

///! The WebAssembly runtime. This module executes compiled programs.

pub struct Runtime {
    // An engine stores and configures global compilation settings like
    // optimization level, enabled wasm features, etc.
    engine: Engine,

    // A `Store` is what owns instances, functions, globals, etc. All wasm
    // items are stored within a `Store`, and it's what we'll always be using to
    // interact with the wasm world. Custom data can be stored in stores and
    // this store stores WASI context used to communicate with the WASI host API.
    store: Store<WasiCtx>,

    modules: Vec<(Module, ModuleSource)>,
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
pub enum RuntimeError {
    #[error(transparent)]
    Trap(#[from] Trap),

    // wasmtime uses `anyhow` so we have to handle this error type
    #[error(transparent)]
    Any(#[from] anyhow::Error),
}

impl Runtime {
    pub fn new() -> Result<Runtime, anyhow::Error> {
        let engine = Engine::default();

        // configure WASI and add it to the store
        let wasi = WasiCtxBuilder::new()
            .inherit_stdio()
            .inherit_args()?
            .build();
        let store = Store::new(&engine, wasi);

        Ok(Runtime {
            engine,
            store,
            modules: vec![],
        })
    }
    /// Compiles a module for later use during execution.
    /// The order that add_module is called determines the order of linking.
    /// The last module added must contain the function to be called by eval(function_name).
    pub fn add_module(&mut self, source: ModuleSource) -> Result<(), RuntimeError> {
        self.modules
            .push((Module::new(&self.engine, &source.wasm_text)?, source));
        Ok(())
    }

    pub fn eval(&mut self, function_name: &str) -> Result<ReturnValue, RuntimeError> {
        let mut linker = Linker::new(&self.engine);

        // add WASI module to the linker
        wasmtime_wasi::add_to_linker(&mut linker, |s| s)?;

        module::add_base_to_linker(&mut linker)?;

        // link in our remaining modules in registration order
        for (module, source) in &self.modules {
            linker.module(&mut self.store, &source.name, module)?;
        }

        // an `Instance` represents a real running machine we can interact with.
        let last_module = &self.modules[self.modules.len() - 1];
        let last_source = &last_module.1;
        let instance = linker.instantiate(&mut self.store, &last_module.0)?;
        //let instance = Instance::new(&mut self.store, module, &[])?;

        let top_level = instance
            .get_func(&mut self.store, function_name)
            .unwrap_or_else(|| panic!("`{}` is not an exported function", function_name));

        if let Type::Void = last_source.return_type {
            let result = top_level.call(&mut self.store, &[], &mut []);
            return match result {
                Ok(_) => Ok(ReturnValue::Void),
                Err(trap) => Err(RuntimeError::from(trap)),
            };
        }

        let mut returns = [Val::I64(0)];
        let result = top_level.call(&mut self.store, &[], &mut returns);

        match result {
            Ok(_) => {
                let returned = &returns[0];
                match last_source.return_type {
                    Type::Int64 => {
                        if let Val::I64(i) = returned {
                            Ok(ReturnValue::Integer(*i))
                        } else {
                            Err(RuntimeError::Any(anyhow::Error::msg("type mismatch")))
                        }
                    }
                    Type::Bool => {
                        if let Val::I32(b) = returned {
                            Ok(ReturnValue::Bool(*b != 0))
                        } else {
                            Err(RuntimeError::Any(anyhow::Error::msg("type mismatch")))
                        }
                    }
                    Type::Void => unreachable!(),
                    Type::Unknown => unreachable!(),
                    Type::Function { .. } => Err(RuntimeError::Any(anyhow::anyhow!(
                        "entry point cannot return a function"
                    ))),
                }
            }
            Err(trap) => Err(RuntimeError::from(trap)),
        }
    }
}

#[cfg(test)]
mod tests {
    use thiserror::Error;

    use crate::compiler::Compiler;
    use crate::runtime;
    use crate::runtime::{ReturnValue, RuntimeError};

    #[derive(Error, Debug)]
    pub enum TestError {
        #[error(transparent)]
        Runtime(#[from] RuntimeError),
        #[error(transparent)]
        Any(#[from] anyhow::Error),
        #[error("{msgs:?}")]
        Other { msgs: Vec<String> },
    }

    /// takes a string of source code and executes it.
    /// Simplified error handling for tests.
    fn run(expr: &str) -> Result<ReturnValue, TestError> {
        let mut runtime = runtime::Runtime::new()?;

        // Compile from our source language to the wasm text format (wat)
        let compiler = Compiler::new();
        let result = compiler.compile_expression("test", expr);
        match result {
            Ok(source) => {
                runtime.add_module(source)?;
                Ok(runtime.eval("main")?)
            }
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
            "{let foo = 1;}" => ReturnValue::Void
            // shadowing
            "let foo = 1; let bar = { let foo = 2; foo }; foo + bar " => ReturnValue::Integer(3)
            "let a = 1; let b = { let a = 2; {let b = 9;} a }; let c = { let d = 4; d }; a + b + c " => ReturnValue::Integer(7)
        }
    }

    #[test]
    fn direct_call() {
        returns! {
            "print_num(1)" => ReturnValue::Void
            "itoa(0)" => ReturnValue::Integer('0' as i64)
            "print_num(itoa(0))" => ReturnValue::Void
        }
    }

    #[test]
    fn indirect_call() {
        returns! {
            "let foo = itoa; foo(1)" => ReturnValue::Integer('1' as i64)
            "let foo = itoa; foo(1)" => ReturnValue::Integer('1' as i64)
        }
    }
}
