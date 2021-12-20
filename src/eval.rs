use crate::compiler::ThunkSource;
use std::fmt;
use std::fmt::{Display, Formatter};
use thiserror::Error;
use wasmtime::*;

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
    Integer(i64),
}

impl Display for ReturnValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ReturnValue::Integer(i) => write!(f, "{}", i),
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

    pub fn eval(&mut self, thunk_source: &ThunkSource) -> Result<ReturnValue, EvalError> {
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

        let top_level = top_level.typed::<(), i64, _>(&self.store)?;

        match top_level.call(&mut self.store, ()) {
            Ok(result) => Ok(ReturnValue::Integer(result)),
            Err(trap) => Err(EvalError::from(trap)),
        }
    }
}
