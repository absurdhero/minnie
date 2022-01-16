use insta;
use minnie::compiler;

///! Verify parse tree and assembly output of a compiled program
///!
///! Run `cargo insta review` to review and accept/reject differences.
///! Install `insta` with `cargo install cargo-insta`.

#[test]
// parse and compile samples and verify their output has not changed
fn test_samples() {
    insta::glob!("samples/*.min", |path| {
        let name = path.file_stem().unwrap().to_str().unwrap();
        let source = std::fs::read_to_string(path).unwrap();

        // Parse trees can be large so these are disabled.
        // Uncomment to generate and inspect parse trees when bisecting bugs
        // but do not commit the results.

        //use minnie::ast::parse_module;
        //let parsed = parse_module(&source).map(|m| m.functions);
        //insta::assert_ron_snapshot!(format!("parse_{}", name), parsed);

        let compiler = compiler::Compiler::new();
        let result = compiler.compile(name, &source);
        match result {
            Ok(module) => {
                insta::assert_snapshot!(format!("compiled_{}", name), module.wasm_text, &source)
            }
            Err(e) => insta::assert_ron_snapshot!(format!("compiled_{}", name), e),
        }
    });
}
