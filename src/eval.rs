use crate::compiler::Compiler;
use anyhow::Result;
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

impl Eval {
    pub fn new() -> Result<Eval> {
        let engine = Engine::default();
        let store = Store::new(&engine, ());
        Ok(Eval { engine, store })
    }

    pub fn eval(&mut self, program: &str) -> Result<()> {
        // Compile from our source language to the wasm text format (wat)
        let compiler = Compiler::new();
        let wat = compiler.compile(program);

        // Create a `Module` which represents a compiled form of our
        // input. In this case it will be JIT-compiled after
        // we parse the text returned by the compiler.
        let module = Module::new(&self.engine, wat)?;

        // With a compiled `Module` we can then instantiate it, creating
        // an `Instance` which represents a real running machine we can interact with.
        let instance = Instance::new(&mut self.store, &module, &[])?;

        let top_level = instance
            .get_func(&mut self.store, "top_level")
            .expect("`top_level` was not an exported function");

        let top_level = top_level.typed::<(), i32, _>(&self.store)?;

        let result = top_level.call(&mut self.store, ())?;
        println!("Returned Number: {:?}", result);
        Ok(())
    }
}
