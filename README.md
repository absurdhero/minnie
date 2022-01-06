# Minnie - Programming Language



## Modules


### Core

The library shared by the compiler and runtime which implements
compilation and execution.

### Compiler

Compiles a program to wasm. It only targets the minnie runtime
but it could target browser runtimes in the future.

### Runtime

Runs a compiled program and can also compile and run a source file.

### REPL

An experimental REPL that doesn't support much of the language yet.
