# Design

## Motivation

All languages are designed with a particular style of programming in mind. This
language attempts to take the best ideas of our present time and carefully tie
them together into a whole that delights us as programmers; Something more
satisfying and productive than the most popular languages; Highly approachable,
safe, and familiar yet powerful and state-of-the-art.

Let's take a look at what makes a good programming language. Programmers make
conscious decisions about language choice based on a many factors. Which factors
are important depend on whether they work on projects big or small, on teams big
or small, and on who will end up using the software they write. Are you writing
software for your own use or for end-users? For servers in the cloud? For
running interactively? The context makes a big difference.

The main factors I see developers thinking about in the open-source
community and commercially include:

- Economy of writing
  - Typing less is better. Except when it gets in the way of other things
      like readability.
  - Semantic complexity
  - Brevity vs Verbosity
- Easy of learning the language
  - Familiarity (compared to past experiences)
  - Documentation
  - Language complexity (primarily governed by type system, abstractions,
    syntax)
- Program safety
    - Type systems
    - Handling null types
    - Error propagation
- Tooling
  - Compiler error messages
  - Build system
  - Library management
  - Editor support
- Scalability - These matter much more for large programs
  - Modularity (e.g. powerful import system and encapsulation)
  - Static Analysis using other tools
- Performance


Social factors that are more difficult to study include:

- Community
  - Open decision processes
  - Accessible forums for socialization and learning for users
- Growth and Maturity
  - Responsive to community feedback
  - Large number of people effectively involved in language and library evolution


## How `minnie` can meet these needs

### Program safety

1. A static type system with algebraic types and good modularization features.

Minnie aims to have a type system on par with rust in its expressiveness.
However, type inference will be more powerful which means types don't need
to be specified nearly as often. Writing out your types will feel more
like an option and less like a requirement. This allows individuals and teams
to make a decision about how much they want types to appear in their code.

Technology should play a role too. Why can't a code formatter add types to
your function signatures so you don't have to?

2. No uninitialized values and nothing can be `null`.

NullPointerException and Segmentation Fault belong in the past. Null can be
replaced by an `Option` type as found in functional languages which has proven
to be safe and usable.

3. Clear and convenient error handling. No possible error should go unnoticed.

The Result type in functional languages is very good for making it obvious
when a function might fail and making it easy to propagate errors without
messing up the readability and flow of code. Making it readable and convenient
requires some special help from the language such as rust's `?` operator
which automatically returns an error up to the caller, keeping code sequential.
Good Result handling is essential but more research is needed to see if
there are even better alternatives than `?`.

### Readability

1. On extremely terse or macro-heavy programs.

Allowing programmers to pack too much meaning and behavior in a few characters
also allows them to over-fit their abstractions to the problem they are trying
to solve. An over-fit model is difficult to change and may fail in non-obvious
ways. Furthermore, language feature that let you change the meaning of regular
syntactic forms reduces readability for new members of a project, even if they
already know the language. When a programmer modifies a language in a way that
changes the meaning of its existing semantics, such as through the unrestricted
use of macros, it becomes impossible to understand whether the program is even
correct!

Examples:

1. User-defined infix operators

   In ML and Haskell, the programmer can create their own infix operators using
   multiple non-alphanumeric characters with their choice of operator
   precedence (from 0-9). Relying on these complex semantics requires carefully
   tuning operator precedence and operator names whenever the system changes.

   In Haskell, it is customary to create two-three symbol characters for
   operating on your own types. And In Scala, a language inspired by Haskell,
   the popular build system, SBT, has a complete DSL (domain-specific language)
   built on user-defined operators.[^sbt]

2. Macros as a primary abstraction mechanism
  
    Macros are popularly considered to be the sign of a powerful language. I
    do not disagree, but I think that languages are not well-designed that
    lean on user-written macros to make up for a dearth of well-considered and
    standardized support for such features as a boolean types[^bool],
    type checking, or a module system.

   On the other hand, rust gets a lot of value from macros by providing would-be
   language features as macros (such as the `Debug` derive macro)
   in its standard library and offers structured and well-documented macro
   abilities to users. I think rust uses macros for good by resisting the
   temptation to push all language features off to macros, offering solutions to
   common patterns, and cultivating widely used packages like `thiserror`
   and `anyhow` that improve the readability of rust programs without causing
   each programmer to reinvent their own common macros. One reason why macros
   in rust are not terribly abused is that they are carefully limited in power.
   There are limits on accessing variables at the call site, limits to the
   syntax (all macro invocations end in `!`), and they are hygienic.

[^sbt] An [example from a popular project](https://github.com/playframework/playframework/blob/master/build.sbt)
  uses `++`, `++=`, `%`, `:=`, `:+`, `**`, `||`, and `/`, in novel ways for
  its file and dependency operations. These save a few characters but have their
  own precedence rules and are not obvious to a developer learning the build
  system, or indeed, a seasoned developer writing one from scratch trying to
  use a search engine to remind them of what one of these operators does.

[^bool] C does not have boolean true and false. `#define TRUE 1`? Sure,
  but now the type system can't tell if you accidentally passed a number to
  something that expects a bool. Using a macro is the best thing to do
  in this case but the more you macro, the more you invent your own private
  language.


### Easy of learning

For a language to be used, programmers first have to learn it. Anything we
can do to reduce the quantity and speed with which programmers have to
acquire new knowledge helps. They shouldn't need a cheatsheet for typing
common arithmetic operators[^pervasives] or how to type a negative number
[^negation].

[^pervasives] https://caml.inria.fr/pub/old_caml_site/ocaml/htmlman/libref/Pervasives.html

[^negation] https://stackoverflow.com/questions/8984661/unary-minus-and-floating-point-number-in-ocaml

If we really want experienced programmers to feel like they are
effortlessly learning the language, their intuition about the width of integers,
how semicolons work (if present), and how to name things should feel natural
from previous experience. While all of these must be documented for
beginners and programmers who don't happen to have used the most popular
programming languages, the less the docs must be consulted, the better.

#### Memory Management

Managing mutable state is one of the most complex tasks when writing software.
It is difficult to analyze at compile time, even more difficult for humans
to reason about, and
The study of the Bronze garbage collector for rust demonstrated that novice
programmers have a much easier time writing a program in rust in the presence
of a garbage collector as compared to using `Rc<RefCell<_>>`[^bronze]. The
paper goes on to claim that rust is not gaining much popularity. I take issue
with the sources of data backing that claim and rust is not attempting
to compete with the most popular languages: Java, Javascript, and Python. It
serves a different purpose.

However, `minnie` _is_ attempting to be safer and more statically analyzable
(with more opportunity for performance optimization) than those popular and
easy-to-learn languages without sacrificing ease-of-use[^static-typescript].

[^bronze] [Does the Bronze Garbage Collector Make Rust Easier to use?](https://arxiv.org/pdf/2110.01098.pdf)

[^static-typescript] Developers are shown to be more productive when
  learning a new API in Typescript with static typing vs. Javascript.
  [ACM publication](https://dl.acm.org/doi/abs/10.1145/2936313.2816720)

## Language

Language properties:

- Statically typed
- Automatic Memory Management (perhaps with a garbage collector)
- Stack allocated values in the common case -- less GC activity
- Mutability is explicit
- Rust and ML inspired syntax with the goal of being familiar to contemporary
  programmers.
- The type system's design is TBD
- No planned support for continuations or exceptions. Limited forms of
  continuation such as async features warrant exploration.

## Compiler

The overall design of the compiler is in flux though it is shaping up to look a
lot like other compilers. The author has researched past and current SML/NJ
architectures, the current rust compiler design, and academic efforts including
nanopass compiler designs. One thing is for certain: Every compiler design
differs for non-technical reasons, and they all solve similar problems despite
their differences. The conclusion for this project is that it may as well evolve
organically as all industrial compilers have before it.

## Runtime

The compiler currently targets WebAssembly which makes a great IR
(intermediate language). WebAssembly provides an implicit stack, improved memory
safety, and limited type safety at the instruction level.

For now, the compiler only emits WebAssembly which means you need a runtime or a
wasm->native compiler to execute it. The project ships with a runtime built on
top of `wasmtime` which provides a portable abstraction over the bare metal.

Wasmtime offers both ahead-of-time and just-in-time compilation. Both are
potential targets but ahead-of-time compilation is the first priority.

### Memory Management

Short-lived local variables don't require any memory management as they
can live exclusively on the stack. Additionally, monomorphization and
careful lifetime analysis can even make it possible to make arrays and maps
store sized data directly inside the data structure instead of keeping pointers
to elements on the heap. This would be a big departure from Java, LISP, and
many other languages with memory management but is a familiar concept to
golang and rust users.

Despite the language being statically typed, types need to be known at
runtime to know how to traverse and free data. There are two options for
tracking type information:

1. There are clever tag-free techniques that don't actually store any type
   information with data instances (see the GC section of references.md)
   but instead store tables that define each type out-of-band. Implementation
   complexity is unknown and some sample implementations will need to be
   evaluated for feasibility.

2. The tried-and-true tagging of all data which is popular with statically
   typed languages like ML (as noted in CS-TR-329-91, Appel 1991). If we go the
   tagging route, data in the heap would be prefixed with one word which
   contains the type, gc flags, and may contain other metadata. While this uses
   more heap space than embedding tags in spare bits inside each item of data,
   it also doesn't require extra work to mask out tag bits before using it.
   Embedded tags may not interact well with WebAssembly's own type system
   anyway.
