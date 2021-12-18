pub struct Compiler {}

impl Compiler {
    pub fn new() -> Compiler {
        Compiler {}
    }

    /// compiles a program in the webassembly wat format
    pub fn compile(&self, program: &str) -> String {
        format!(
            r#"
        (module
          (func (export "top_level") (result i32)
             i32.const {}
          )
        )
        "#,
            program
        )
    }
}
