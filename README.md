# Minnie

[![Build Status](https://github.com/absurdhero/minnie/actions/workflows/build.yml/badge.svg)](https://github.com/absurdhero/minnie/actions)

Minnie is programming language designed for productive and safe software
development that uses advanced features to make programming less
frustrating and great for large, collaborative, code-bases.

Goals:
 - Familiar rust-like syntax but without lifetimes
 - Statically typed but with optional type annotations --
   You only specify types if you want
 - An efficient runtime with minimal garbage collection
 - Easy to learn with great documentation
 - Integrate with the rust ecosystem
 - Built for the cloud:
   - run security and efficiently on serverless compute platforms
   - statically linked binaries with fast startup times
   - run in browsers as WebAssembly

See the draft [design doc](doc/design.md) for more info about
where the language is heading and a list of [references](doc/references.md) 
that influence how the language is implemented.

### Getting Started

Example: `hello.min`
```rust
// This is a very early example. We don't have strings yet!
fn factorial(num: int) -> int {
    if num == 1 {
        1
    } else {
        num * factorial(num - 1)
    }
}

pub fn main() {
    print_num(factorial(3));
}
```

This project requires a rust toolchain to build the software. If you don't
have rust, you can get it at [rustup.rs] or you can run the installer with:
```commandline
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

Now you can check out this project from git and get started.

Compile and run `hello.min` in one step with:
```
cargo run -- hello.min
```

To compile the source file into the wasm format, run the compiler through cargo:
```
cargo run -p minnie-compiler -- hello.min
```
This outputs `hello.minw` which contains WebAssembly source.

## Participating

I welcome contributors, potential partners, and fellow enthusiasts who just want
to leave a comment. This project is in its infancy so there is no GitHub
Organization or foundation set up to administer it and no Code of Conduct. But
if people express an interest in this work, I will enthusiastically set up an
Organization and make it "ours", not "mine". Please don't let the fact that one
person began the project stop you from sharing in its future ownership and
community.

There are plenty of easy tasks that I have set aside for someone looking for 
a small thing to poke at and get merged in. Open an issue, PR, or email me 
to get started.

## Code Layout

### Core

This library is shared by the compiler and runtime. It implements
compilation and execution.

### Compiler

Compiles a program to WebAssembly. It only targets the minnie runtime
but it will also target browsers in the future.

### Runtime

Runs a program. If you give it a source file, it will compile and then run it.

### REPL

An experimental REPL that doesn't support much of the language yet.
