# References

## Compiler Design

Papers and Articles that influence the design of the compiler and runtime environment.

[Standard ML of New Jersey (CS-TR-329-91); Appel](https://www.cs.princeton.edu/~appel/papers/smlnj.pdf)
- A look inside a statically typed functional language implementation.

[A New Backend for Standard ML of New Jersey (Draft); Farvardin, Reppy](https://people.cs.uchicago.edu/~jhr/papers/2020/ifl-smlnj-llvm.pdf)
- A recent report on SML/NJ moving its backend to LLVM.

[Guide to Rustc Development](https://rustc-dev-guide.rust-lang.org)
- Rust compiler internals. What other compiler has such approachable docs?

[Rust Reference](https://doc.rust-lang.org/stable/reference/)
- Definition of the rust language. Detailed descriptions of the grammar.

# Language Design

[A critique of Standard ML; Appel](https://www.cs.princeton.edu/~appel/papers/critique.pdf)
- An aggregated list of critiques about ML and thoughtful responses.

## Type Theory

[Intro to Type Theory](https://mukulrathi.com/create-your-own-programming-language/intro-to-type-checking/)
- An accessible introduction to type theory and type checkers.

[Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism; Dunfield, Krishnaswami](https://www.cl.cam.ac.uk/~nk480/bidir.pdf)
- A type inference algorithm. See also: implementations for
[Rust](https://github.com/JDemler/BidirectionalTypechecking),
[JavaScript](https://github.com/atennapel/bidirectional.js)
and [Haskell](https://github.com/ollef/Bidirectional).

## Garbage Collection

[A Unified Theory of Garbage Collection; Bacon](https://courses.cs.washington.edu/courses/cse590p/05au/p50-bacon.pdf)

[Programming with Regions in ML Kit](https://elsman.com/mlkit/pdf/mlkit-4.3.0.pdf)
- A very different approach to memory allocation using lifetime analysis
  and very little GC activity.

[Rust as a language for high performance GC implementation; Lin](https://dl.acm.org/doi/10.1145/2926697.2926707)

[Does the Bronze Garbage Collector Make Rust Easier to use?; Coblenz](https://arxiv.org/pdf/2110.01098.pdf)

Techniques for implementing garbage collection in a statically typed language without tagging data in memory.
- [Runtime Tags Aren't Necessary; Appel](https://www.cs.princeton.edu/~appel/papers/142.pdf)
- [Tag-Free Garbage Collection; Goldberg](https://cs.nyu.edu/~goldberg/pubs/gold91.pdf)
- [Tag-free Garbage Collection Using Explicit Type Parameters; Tolmach](https://www.cs.tufts.edu/~nr/cs257/archive/andrew-tolmach/tag-free-gc-as-published.pdf)

## WebAssembly

Reference material for understanding and targeting WebAssembly.

[MDN: Understanding WebAssembly text format](https://developer.mozilla.org/en-US/docs/WebAssembly/Understanding_the_text_format) -
A good introductory walk-through of WebAssembly in its text form.

[WebAssembly Reference Manual](https://github.com/sunfishcode/wasm-reference-manual/blob/master/WebAssembly.md) -
An explanatory reference that compliments the spec.

[WebAssembly Specification 1.1](https://webassembly.github.io/spec/core/_download/WebAssembly.pdf) -
The official specification. Terse and contains little explanation.

[Rust and WebAssembly](https://rustwasm.github.io/docs/book/introduction.html) -
Practical techniques for working with WebAssembly using rust and cargo.

[A Practical Guide to WebAssembly Memory](https://radu-matei.com/blog/practical-guide-to-wasm-memory/)

## Miscellaneous

Writings that people interested in this project may also find interesting.

[Fast String Interning in Rust](https://matklad.github.io/2020/03/22/fast-simple-rust-interner.html)

