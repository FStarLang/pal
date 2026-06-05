# PAL

PAL is a transpiler from C to [Pulse](https://github.com/fstarlang/pulse) (a verification-oriented language built on [F*](https://github.com/fstarlang/fstar)). It parses C source files using libclang (via a C++ frontend), translates them through an intermediate representation (IR), and emits verified Pulse `.fst` files.

## Build & Test

Requires clang >= 20, LLVM development headers, and `llvm-config` on `PATH`.

```sh
# Build everything (Rust binary + Pulse support library)
make

# Build only the Rust binary
cargo build

# Run all tests (builds first, then verifies generated .fst files with F*)
make test -j8

# Run a single test by translating a C file directly
cargo run -- test/swap.c          # produces Swap.fst, Swap_diagnostics.json, Swap_source_range_info.json
cargo run -- --print-ir test/swap.c  # print the IR without emitting files

# Formatting (CI checks this)
cargo fmt
clang-format -i cpp/impl.cpp
```

The test suite (`test/Makefile`) runs `pal` on each `.c` file in `test/`, then verifies the generated `.fst` files using F*/Pulse.

ALWAYS RUN `make test -j8` TO MAKE SURE THE TESTS SUCCEED!!!

Please commit your changes once you're done!

NEVER RUN `git remote set-url`.  You are probably running in a sandbox with restricted permissions, it's expected that `git push` doesn't work.

## Architecture

### Translation Pipeline

The main pipeline (`src/main.rs`) processes each C file through sequential passes:

1. **Parse** (`src/clang.rs` + `cpp/impl.cpp`) — libclang parses C into the IR. The C++ side (`cpp/impl.cpp`) walks the Clang AST and calls Rust constructors to build IR nodes. Rust/C++ interop uses [Zngur](https://github.com/nickel-org/zngur), configured in `cpp/iface.zng`.
2. **Check** (`src/pass/check.rs`) — IR well-formedness validation, run after each transformation pass.
3. **Prune** (`src/pass/prune.rs`) — Removes declarations not from the main file.
4. **Elab** (`src/pass/elab.rs`) — Type elaboration and checking.
5. **Emit** (`src/pass/emit.rs`) — Generates Pulse `.fst` code from the IR.

### IR (`src/ir/`)

The IR is a typed AST modeling C constructs (types, expressions, statements, declarations). Key patterns:
- Every AST node is wrapped in `Ast<T>`, pairing a value with source location info (`Rc<SourceInfo>`).
- Tree nodes are reference-counted (`Rc<Ast<T>>`), with type aliases: `Type = Ast<TypeT>`, `RValue = Ast<RValueT>`, `Stmt = Ast<StmtT>`, etc.
- The `WithLoc` trait provides `.with_loc(loc)` for constructing located AST nodes.

### Zngur FFI (`cpp/iface.zng`)

Defines the Rust/C++ boundary. The C++ code calls Rust functions declared here to construct IR nodes. Changes to IR types typically require updating `iface.zng` and `cpp/impl.cpp` in tandem.

### PAL Header (`pal.h`)

C source files include `pal.h` to use verification annotations. When `C2PULSE` is defined (during translation), these macros expand to clang attributes; otherwise they are no-ops so the code compiles normally with any C compiler:
- `_requires(p)`, `_ensures(p)` — pre/postconditions
- `_invariant(p)` — loop invariants
- `_plain`, `_consumes` — ownership annotations on parameters
- `_include_pulse(...)` — inline Pulse code
- `_old(x)`, `_live(x)`, `_specint`, `_slprop` — specification-level constructs

### Diagnostics

Diagnostics are emitted as LSP-compatible JSON (`*_diagnostics.json`) alongside generated code, enabling IDE integration. Errors are also printed to stderr using `codespan-reporting`.

## Key Conventions

- Rust edition 2024; uses `chumsky` for parsing inline Pulse expressions (`src/hauntedc.rs`).
- The `pretty` crate is used for Pulse code emission with source range tracking.
- Output file names are derived from input: `foo.c` → `Foo.fst` (first letter capitalized).
- Test C files live in `test/<name>/<name>.c`; each must include `pal.h` and contain verification annotations.
- In each test subfolder (`test/<name>/`), the header files and Makefile must be symlinks, not real files. Specifically:
  - `pal.h` → `../pal.h`
  - `Makefile` → `../_templates/Makefile`
  - `fstar.fst.config.json` → `../_templates/fstar.fst.config.json`
  - `pal.config.json` → `../_templates/pal.config.json`
  Create new test folders by running the `test/new.sh test_name` script so these symlinks are set up correctly.
- The `pulse/` directory contains F*/Pulse library files (`.fst`/`.fsti`) for C interop types.
