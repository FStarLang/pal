# Internals

This document describes how PAL processes a C source file into
verified Pulse/F* code. The pipeline follows the same
parse, lower, check, emit progression found in production compilers,
applied here to translating C with proof annotations into a
separation-logic-based verification language.

---

## 1. From C to Verified Pulse

A PAL run has seven passes. Each transforms a typed intermediate
representation until the final pass emits Pulse code that F* can
verify.

```
 .c --> Parse --> Prune --> Merge --> Restructure --> Decay --> Elab --> Emit --> .fst
        libclang   drop     join     goto to           array    type    Pulse
        + Zngur    extern   fwd      structured        decay    check   codegen
                   decls    decls    control flow
```

The `Check` pass is not shown in the diagram because it is not a
transform -- it is a well-formedness validator that runs twice: once
after prune and once after elab. If check finds an inconsistency, it
reports a diagnostic and the pipeline continues with best-effort output.

- **Parse.** [`src/clang.rs`](../src/clang.rs) invokes libclang to parse the C source.
A C++ frontend ([`cpp/impl.cpp`](../cpp/impl.cpp)) walks the resulting Clang AST and
calls Rust constructors through a [Zngur](https://github.com/HKalbasi/zngur)
FFI boundary ([`cpp/iface.zng`](../cpp/iface.zng)) to build IR nodes. Each Clang AST node
maps to one or more IR nodes. The parser also invokes [`hauntedc.rs`](../src/hauntedc.rs)
(a [chumsky](https://github.com/zesterer/chumsky)-based parser) to
parse inline Pulse expressions embedded in `_inline_pulse(...)` and
similar annotation macros.

- **Prune.** [`src/pass/prune.rs`](../src/pass/prune.rs) walks the declaration list and drops
everything that does not originate from the main source file. This
removes system headers, standard library prototypes, and anything
pulled in by `#include` that is not the user's code.

- **Merge.** [`src/pass/merge.rs`](../src/pass/merge.rs) joins forward declarations with their
corresponding definitions. A `struct foo;` followed by
`struct foo { int x; }` becomes a single `StructDefn` node.

- **Restructure goto.** [`src/pass/restructure_goto.rs`](../src/pass/restructure_goto.rs) eliminates `goto`
statements. The pass scans for label/goto pairs from the bottom of each
statement list and wraps the intermediate code in `GotoBlock` nodes --
structured loops with break semantics that Pulse can express. Labels
that no goto references are left as-is and removed later.

- **Decay.** [`src/pass/decay.rs`](../src/pass/decay.rs) handles C's array-to-pointer decay
rule for function parameters. A parameter declared as `T x[]` or
annotated with `_array` is rewritten from `FixedArray(T, N)` to
`Pointer(T, Array)` so that the emitter can generate the correct
`array_pts_to` separation logic predicates.

- **Elab.** [`src/pass/elab.rs`](../src/pass/elab.rs) is the largest pass. It resolves
`TypeT::Unknown` placeholders left by the parser, infers expression
types, checks type compatibility, elaborates implicit casts (integer
promotions, pointer conversions), and fills in default ownership
annotations for function parameters that lack explicit `_plain`,
`_consumes`, or `_out` markers.

- **Emit.** [`src/pass/emit.rs`](../src/pass/emit.rs) lowers the fully elaborated IR into Pulse
source code. Each top-level declaration produces its own `.fst` module
(and optionally a `.fsti` interface). The emitter uses the `pretty`
crate for layout and tracks source range mappings so that positions
in the generated Pulse can be traced back to the original C.

---

## 2. The Intermediate Representation

The IR is a typed AST that models C constructs at a level of
abstraction between Clang's AST and Pulse's syntax. All node types
live in [`src/ir/mod.rs`](../src/ir/mod.rs).

### Node wrapper

Every AST node is an `Ast<T>`: a value `T` paired with source location
information.

```rust
pub struct Ast<T> {
    pub val: T,
    pub loc: Rc<SourceInfo>,
}
```

Trees are reference-counted with `Rc<Ast<T>>`. Type aliases keep
things readable throughout the codebase:

```rust
pub type Type  = Ast<TypeT>;      // int, bool, pointer, struct ref, ...
pub type Expr  = Ast<ExprT>;      // variables, literals, operations, calls
pub type Stmt  = Ast<StmtT>;      // assignments, if/while, return, goto
pub type Decl  = Ast<DeclT>;      // functions, structs, typedefs, globals
pub type Ident = Ast<Rc<IdentT>>;  // identifiers (IdentT = str)
```

The `WithLoc` trait provides `.with_loc(loc)` to wrap a bare value
into a located `Rc<Ast<T>>` in one call. `reuse_loc` on an existing
node re-uses its location for a new value, which is common when a pass
rewrites a node in place.

### Types

`TypeT` covers C's type system plus PAL's verification extensions:

| Variant | Represents |
|---------|-----------|
| `Void`, `Bool`, `Int { signed, width }` | C scalar types |
| `SizeT`, `PtrdiffT` | platform-dependent integer types |
| `Pointer(T, PointerKind)` | pointer with ownership classification: `Ref`, `Array`, `ArrayPtr`, or `Unknown` |
| `FixedArray(T, N)` | C array type `T[N]`, decayed by the decay pass |
| `SpecInt`, `SpecNat`, `SLProp` | ghost types for specifications |
| `TypeRef(kind)` | named reference to a struct, union, or typedef |
| `Refine`, `RefineAlways`, `RefineUninit`, `RefineValue` | refinement types from `_refine*` annotations |
| `Plain(T)` | strip default ownership from `T` |
| `Unknown` | placeholder resolved during elaboration |
| `Error` | sentinel for unrecoverable parse errors |

`PointerKind` determines the separation-logic resource that the emitter
generates. `Ref` produces `pts_to`, `Array` produces `array_pts_to`,
and `ArrayPtr` produces `arrayptr_pts_to`.

### Expressions

`ExprT` is a unified lvalue/rvalue expression type:

- **Lvalues:** `Var`, `Deref`, `Member`, `Index`
- **Rvalues:** `BoolLit`, `IntLit`, `Ref`, `UnOp`, `BinOp`, `FnCall`,
  `Cast`, `Malloc`, `Free`, `SizeOf`, `Cond`, ...
- **Verification:** `Live`, `Old`, `Forall`, `Exists`, `InlinePulse`

Operators include the full set of C arithmetic, comparison, logical,
and bitwise operations, plus `Implies` (`==>`) for specifications.

### Statements

`StmtT` covers C's statement forms:

| Variant | C construct |
|---------|------------|
| `Decl(name, type)` | local variable declaration |
| `DeclStackArray(name, type, size)` | stack-allocated array declaration |
| `Assign(lhs, rhs)` | assignment |
| `Call(expr)` | standalone function call (expression statement) |
| `If(cond, then, else)` | conditional |
| `While { cond, inv, body, ... }` | loop with invariants |
| `Return(expr)` | return |
| `Break`, `Continue` | loop control |
| `Goto(label)`, `Label { name, ensures }` | goto/label (before restructuring) |
| `GotoBlock { body, label, ensures }` | structured goto (after restructuring) |
| `Assert(expr)` | `_assert(...)` verification assertion |
| `GhostStmt(code)` | `_ghost_stmt(...)` |
| `Error` | sentinel for unrecoverable parse errors |

### Declarations

`DeclT` enumerates top-level items:

| Variant | C construct | Output module |
|---------|------------|---------------|
| `FnDefn` | function definition | `Func_<name>.fst` (+ `.fsti` for non-pure functions) |
| `FnDecl` | function prototype (no body) | `Func_<name>.fst` (assumed/unreachable body) |
| `StructDefn` | `struct` with fields | `Struct_<name>.fst` |
| `StructDecl` | forward `struct` declaration | (merged by the merge pass) |
| `UnionDefn` | `union` with fields | `Union_<name>.fst` |
| `Typedef` | `typedef` | `Typedef_<name>.fst` |
| `LetDecl` | Pulse let binding (`_let`) | `Let_<name>.fst` |
| `OpaqueTypeDecl` | Pulse type (`_type`) | `Type_<name>.fst` |
| `IncludeDecl` | `_include_pulse(Mod, ...)` | `<Mod>.fst` |
| `GlobalVar` | global variable | `Global_<name>.fst` |

A `TranslationUnit` is the top-level container: a list of
`main_file_names` (the input `.c` files) and a flat list of `Decl`
nodes.

---

## 3. Zngur FFI

PAL's parser needs libclang (a C++ library) but the rest of the
pipeline is Rust. The two languages meet through
Zngur, a tool that generates
type-safe Rust/C++ interop code from an interface definition.

The interface lives in [`cpp/iface.zng`](../cpp/iface.zng). It declares Rust types
(`Rc<Expr>`, `Rc<Type>`, `Rc<SourceInfo>`, ...) and the Rust
constructors the C++ side is allowed to call. Zngur generates:

- `cpp/generated.h` -- C++ headers for calling Rust
- A Rust source file (in the build output) that implements the FFI glue

The C++ frontend ([`cpp/impl.cpp`](../cpp/impl.cpp)) uses these generated bindings to walk
the Clang AST and construct IR nodes. A typical pattern:

1. Clang visits a function declaration
2. `impl.cpp` extracts the name, return type, parameters, and body
3. For each, it calls Rust constructors like `TypeT::Int { signed, width }.with_loc(loc)`
4. It assembles a `FnDefn` and pushes it onto the declaration list

**Changing an IR type requires updating both `iface.zng` and `impl.cpp`
in tandem.** The build will fail if they are out of sync, since Zngur
checks that the C++ calls match the declared Rust signatures.

The build script ([`build.rs`](../build.rs)) orchestrates everything:

1. Runs Zngur on [`cpp/iface.zng`](../cpp/iface.zng) to produce the generated files
2. Compiles [`cpp/impl.cpp`](../cpp/impl.cpp) with the LLVM/Clang C++ flags from `llvm-config`
3. Links against `libclang-cpp`

---

## 4. Diagnostics

PAL produces diagnostics in two formats:

- **Stderr.** Human-readable error messages printed via
[codespan-reporting](https://github.com/brendanzab/codespan-reporting),
which renders source snippets with underlined ranges and error labels.
The virtual filesystem ([`src/vfs.rs`](../src/vfs.rs)) provides file contents for the
renderer.

- **JSON.** LSP-compatible diagnostics written to `diagnostics.json`,
grouped by source file URI (`file://...`). Each entry is an
`lsp_types::Diagnostic` with range, severity, and message. This
enables IDE integration: an editor can load the JSON and display
inline error markers on the C source.

Source range tracking ([`src/source_range_info.rs`](../src/source_range_info.rs)) maps positions in
the generated Pulse output back to positions in the original C file.
This is written to `source_range_info.json` alongside the `.fst`
output.

---

## 5. Output Structure

For a C file containing a function `swap` and a struct `point`, PAL
emits:

```
out/
  Func_swap.fst             function implementation
  Func_swap.fsti            function interface (signature + contract)
  Struct_point.fst          struct type, predicates, fold/unfold, field accessors
  TranslationErrors.fst     asserts False if any translation errors occurred
  diagnostics.json          LSP-compatible diagnostics
  source_range_info.json    Pulse-to-C position mapping
```

`TranslationErrors.fst` is a sentinel module. When the translation
has errors, it contains `let _ = assert False`, which makes F* report
a verification failure. When there are no errors, the module contains
only the `module TranslationErrors` header with no assertions.
This way, running F* on the output directory always surfaces
translation problems without requiring a separate error-checking step.

---

## 6. The Pulse Support Library

Generated code depends on a set of F*/Pulse modules in [`pulse/`](../pulse/) that
define C interop types. These are not generated -- they are
hand-written library code that ships with PAL.

| Module | What it provides |
|--------|-----------------|
| `Pulse.Lib.C.Ref` | mutable reference (`ref T`) with `pts_to` |
| `Pulse.Lib.C.Array` | arrays with `array_pts_to`, `array_pts_to_full`, `arrayptr_pts_to` |
| `Pulse.Lib.C.Int32` | `Int32.t` arithmetic |
| `Pulse.Lib.C.UInt32` | `UInt32.t` arithmetic |
| `Pulse.Lib.C.SizeT` | `size_t` operations |
| `Pulse.Lib.C.PtrdiffT` | `ptrdiff_t` operations |
| `Pulse.Lib.C.Casts` | safe casts between numeric types |
| `Pulse.Lib.C.Casts.Bool` | bool-to-integer casts |
| `Pulse.Lib.C.UnaryOps` | negation, bitwise not |
| `Pulse.Lib.C.Sizeof` | compile-time `sizeof` |
| `Pulse.Lib.C.Inhabited` | inhabitedness proofs (needed for memory allocation) |
| `Pulse.Lib.C.Assumptions` | axioms bridging C semantics and F* |

The top-level module `Pulse.Lib.C` re-exports the core subset:
`Inhabited`, `Int32`, `Ref`, `Array`, `Casts`, `UnaryOps`, and `Sizeof`.
Modules like `UInt32`, `SizeT`, `PtrdiffT`, and `Assumptions` must be
opened individually when needed.

---

## Further Reading

| Document | Covers |
|----------|--------|
| [Surface syntax](pal_surface_syntax.md) | Full annotation reference: contracts, ownership, refinements, ghost code, Pulse interop |
| [Structs](structs.md) | What PAL emits per `struct` and `union`: generated types, predicates, fold/unfold, field projections |
| [doc/README.md](README.md) | Documentation index: how to write specs, how C data is modeled in Pulse |

For a code-level starting point: [`src/main.rs`](../src/main.rs) (pipeline orchestration)
and [`src/pass/emit.rs`](../src/pass/emit.rs) (the authoritative lowering when in doubt).
