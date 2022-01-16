# Acceptance Test Suite

The tests in this sub-project use the public interfaces of the core library to
test the parser, compiler, and runtime.

At the moment, all of the tests use the `insta` library to store snapshots
of previously confirmed results. If the parse tree or wasm output of a test changes, the test will fail.

If a test fails, you can inspect and update the result.

    Install `insta` with `cargo install cargo-insta`.

    Run `cargo insta review` to review and accept/reject differences.

    Commit the updated snapshots.
