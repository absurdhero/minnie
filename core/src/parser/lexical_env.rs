use crate::module::ModuleEnv;
use crate::types::{Type, ID};
use std::cell::RefCell;
use std::collections::HashMap;

#[derive(Debug)]
pub struct LexicalEnv<'a> {
    // association of symbol to its unique ID and type
    bindings: RefCell<HashMap<String, (ID, Type)>>,
    parent: Option<&'a LexicalEnv<'a>>,
    func_count: usize,
    var_count: usize,
    imports: &'a ModuleEnv,
}

impl<'a> LexicalEnv<'a> {
    /// Create a new lexical scope inside of another one
    pub fn new(parent: &'a LexicalEnv) -> LexicalEnv<'a> {
        LexicalEnv {
            bindings: RefCell::new(HashMap::new()),
            parent: Some(parent),
            var_count: parent.var_count,
            func_count: parent.func_count,
            imports: parent.imports,
        }
    }

    /// Create an empty top-level lexical environment
    ///
    /// # arguments
    ///
    /// * `module_env` - The imported symbols. This is only being passed into a new lexical env instead
    ///  of being mutated by the env during type checking because the `use` statement does not exist yet.
    ///  Until then, imports are controlled by the runtime a priori and imports are immutable.
    pub fn new_root(module_env: &'a ModuleEnv) -> LexicalEnv<'a> {
        LexicalEnv {
            bindings: RefCell::new(HashMap::new()),
            parent: None,
            var_count: 0,
            func_count: module_env.imports.len(),
            imports: module_env,
        }
    }

    /// Add an identifier for a variable to the environment
    ///
    /// This function also increments a counter used to uniquely identical lexical variables.
    /// WebAssembly tracks `locals` by unique incrementing number so this stage of compilation
    /// assigns numbers to each unique variable.
    ///
    /// We are effectively performing "alpha-conversion", where a variable that shadows another
    /// gets its own ID distinct from the ID of variables by the same name in outer scopes.
    pub fn add_var(&mut self, name: &str, ty: &Type) -> ID {
        let new_id = ID::VarId(self.var_count);
        self.var_count += 1;
        self.bindings
            .borrow_mut()
            .insert(name.to_string(), (new_id.clone(), ty.clone()));
        new_id
    }

    /// Add a new function to the environment
    ///
    /// Functions have their own numeric indexes separate from variables
    /// because webassembly tracks them in their own index space.
    pub fn add_func(&mut self, id: &ID, ty: Type) -> ID {
        let (new_id, name) = match id {
            ID::Name(name) => {
                self.func_count += 1;
                (ID::FuncId(self.func_count - 1), name)
            }
            pub_id @ ID::PubFuncId(name) => (pub_id.clone(), name),
            _ => panic!("tried to add a function with an unsupported ID variant"),
        };
        self.bindings
            .borrow_mut()
            .insert(name.to_string(), (new_id.clone(), ty));
        new_id
    }

    pub fn update_func(&self, name: &str, ty: Type) {
        let mut bindings = self.bindings.borrow_mut();
        let (id, _) = bindings
            .remove(name)
            .expect("could not update lexical mapping for non-existent function");
        bindings.insert(name.to_string(), (id, ty));
    }

    /// Return the unique ID and Type of a variable name in this lexical scope or an outer
    /// scope, ascending upwards through the lexical environment up to the module scope.
    pub fn id_type(&self, name: &str) -> Option<(ID, Type)> {
        self.bindings
            .borrow()
            .get(name)
            .cloned()
            .or_else(|| self.parent.and_then(|p| p.id_type(name)))
            .or_else(|| self.imports.id_type(name))
    }
}
