use crate::types::{Type, ID};
use std::collections::HashMap;
use wasmtime::{Caller, Linker};
use wasmtime_wasi::WasiCtx;

/// Functions accessible to all programs.
///
/// Currently, this just includes some functions for testing.
pub fn add_base_to_linker(linker: &mut Linker<WasiCtx>) -> anyhow::Result<&mut Linker<WasiCtx>> {
    linker.func_wrap(
        "base",
        "print_num",
        |_caller: Caller<'_, WasiCtx>, param: i64| {
            println!("Got {} from WebAssembly", param);
        },
    )?;
    linker.func_wrap("base", "itoa", |param: i64| param + '0' as i64)
}

/// Temporary canned module environment until programs can declare their own imports.
pub fn basis_imports() -> ModuleEnv {
    let mut module_env = ModuleEnv::new();
    module_env.add_import(
        "print_num",
        Type::Function {
            params: vec![Type::Int64],
            returns: Box::new(Type::Void),
        },
    );
    module_env.add_import(
        "itoa",
        Type::Function {
            params: vec![Type::Int64],
            returns: Box::new(Type::Int64),
        },
    );
    module_env
}

/// A module's global environment
#[derive(Debug, Clone)]
pub struct ModuleEnv {
    // association of symbol to its unique index and type
    pub imports: Vec<(String, Type)>,
    pub imports_by_name: HashMap<String, usize>,
}

impl ModuleEnv {
    #[allow(clippy::new_without_default)]
    pub fn new() -> ModuleEnv {
        ModuleEnv {
            imports: vec![],
            imports_by_name: HashMap::new(),
        }
    }

    pub fn add_import(&mut self, name: &str, ty: Type) {
        if self.imports_by_name.contains_key(name) {
            self.imports[*self.imports_by_name.get(name).unwrap()] = (name.to_string(), ty);
        } else {
            self.imports_by_name
                .insert(name.to_string(), self.imports.len());
            self.imports.push((name.to_string(), ty));
        }
    }

    pub fn id_type(&self, name: &str) -> Option<(ID, Type)> {
        self.imports_by_name.get(name).and_then(|i| {
            return self
                .imports
                .get(*i)
                .map(|(_, ty)| (ID::FuncId(*i), ty.clone()));
        })
    }
}
