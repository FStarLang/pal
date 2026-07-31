<div align="center">



<img src="assets/pal-logo.png" alt="PAL" width="321"/>

# PAL


### Proof Annotated Language for C

[![CI](https://github.com/FStarLang/pal/actions/workflows/ci.yml/badge.svg)](https://github.com/FStarLang/pal/actions/workflows/ci.yml)
[![Rust 2024](https://img.shields.io/badge/Rust-2024_edition-DEA584.svg?logo=rust&logoColor=white)](https://www.rust-lang.org/)
[![Clang 20+](https://img.shields.io/badge/Clang-20%2B-262D3A.svg?logo=llvm&logoColor=white)](https://llvm.org/)
[![F\*/Pulse](https://img.shields.io/badge/F*%2FPulse-verified-5B2D8E.svg)](https://github.com/FStarLang/pulse)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

[Quick Start](#quick-start) · [Docs](#documentation)

</div>

---

PAL is a verification framework that lets you write C and prove it correct.
You annotate standard C code with contracts -- preconditions, postconditions,
loop invariants, ownership disciplines -- using macros from [`pal.h`](examples/pal.h), and PAL
handles the rest: it transpiles the annotated source into
[Pulse](https://github.com/FStarLang/FStar/tree/master/pulse) (a separation-logic-based
verification language built on [F\*](https://github.com/FStarLang/fstar)),
where the proofs are discharged automatically by the type checker.

The result is a single C codebase that both compiles with any standard C
compiler _and_ carries machine-checked correctness proofs. When `C2PULSE` is
not defined, all annotations vanish -- the code is plain C.

```c
#include "pal.h"

void swap(int *x, int *y)
    _ensures(*y == _old(*x) && *x == _old(*y))
{
    int tmp = *y;
    *y = *x;
    *x = tmp;
}
```

The `_ensures` annotation states the postcondition: after `swap` returns,
the values are exchanged. PAL translates this into a Pulse function whose
type encodes that contract. F\*/Pulse type-checks the generated code -- if
it passes, the implementation satisfies the spec. More availabe at [`examples/`](examples/).

---

## Quick Start

### Dependencies

| What | Version | Why |
|------|---------|-----|
| Clang / LLVM | 20.x (CI uses `llvm.sh 20`, currently 20.1.8) | libclang parses C |
| LLVM dev headers | 20.x | `llvm-config`, `libclang-cpp20-dev`, `libclang-20-dev` |
| g++ | recent | builds the C++ FFI ([`cpp/impl.cpp`](cpp/impl.cpp)) |
| Rust | 2024 edition | compiles the PAL binary |
| F\*/Pulse | nightly 2026-07-30 | verifies generated `.fst` output |

### Setup (Ubuntu / Debian)

These are the same steps CI runs
(see [`.github/workflows/ci.yml`](.github/workflows/ci.yml)):

```bash
# Clang 20 + LLVM dev packages
wget https://apt.llvm.org/llvm.sh
chmod +x llvm.sh
sudo ./llvm.sh 20
sudo apt update
sudo apt install -y clang-20 libclang-cpp20-dev g++ clang-tools-20 libclang-20-dev

# F*/Pulse nightly (pinned to the version CI uses)
./opt/install-fstar.sh --link-dir /usr/local/bin

# Rust (skip if already installed)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

`llvm-config` (or `llvm-config-20`) must be on `PATH` -- the build script
calls it to find LLVM libraries.

### Build & verify

```bash
make               # Rust binary + Pulse support library
make test -j8      # translate every test case, verify with F*
cd test/swap && make                       # one test
cargo run -- --print-ir test/swap/swap.c   # just the IR
```

82 test directories, each a C file that PAL translates and F\*/Pulse
verifies. Create a new one with `./test/new.sh my_test`.

### Translate a file

```bash
cargo run -- -o out/ myfile.c            # emit .fst files
cargo run -- --print-ir myfile.c         # dump IR, no files written
cargo run -- --time-passes -o out/ myfile.c  # per-pass timing
```

### CLI

```
pal [OPTIONS] <FILES>...

  -o, --outdir <DIR>     where to write .fst output
  -I <PATH>              extra include search paths
      --print-ir         print IR and exit
      --time-passes      show per-pass timing
  -q, --quiet            suppress diagnostics on stderr
      --tmpdir <DIR>     directory for intermediates
```

---

## Documentation

Detailed references live in [`doc/`](doc/):

| Document | Covers |
|----------|--------|
| [Surface syntax](doc/pal_surface_syntax.md) | Full annotation reference: contracts, ownership, refinements, ghost code, Pulse interop |
| [Structs](doc/structs.md) | What PAL emits per `struct` and `union`: generated types, predicates, fold/unfold, field projections |
| [Internals](doc/internals.md) | Pipeline passes, IR design, Zngur FFI, diagnostics, output structure, Pulse support library |
| [doc/README.md](doc/README.md) | Documentation index: how to write specs, how C data is modeled in Pulse |

---

## License

[Apache 2.0](LICENSE)
