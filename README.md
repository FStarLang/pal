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
| F\*/Pulse | nightly 2026-11-06 | verifies generated `.fst` output |

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

### Setup (native Windows)

Use PowerShell 7 and MSYS2's **UCRT64** environment. PAL, Rust, Clang and
F* run as native Windows executables; WSL is not required. Enable Windows
Developer Mode (or clone from an elevated terminal) so Git can create the
test suite's symlinks.

Install these packages from an MSYS2 UCRT64 terminal:

```bash
pacman -Syu
pacman -S --needed make git python mingw-w64-ucrt-x86_64-rust \
  mingw-w64-ucrt-x86_64-clang mingw-w64-ucrt-x86_64-llvm \
  mingw-w64-ucrt-x86_64-clang-tools-extra
git -c core.symlinks=true -c core.autocrlf=false clone https://github.com/FStarLang/pal.git
```

Extract the `fstar-Windows_NT-x86_64.zip` asset from the F*/Pulse nightly
`2026-11-06`. Set the roots in PowerShell (the F* root must contain
`bin\fstar.exe`), then use the launcher:

```powershell
$env:PAL_MSYS_ROOT = 'D:\msys64'
$env:PAL_FSTAR_ROOT = 'C:\tools\fstar'
.\opt\windows.ps1 -Command @('make', 'test', '-j8')
.\opt\windows.ps1 -Command @('target/debug/pal.exe', '--print-ir', 'test/swap/swap.c')
.\opt\windows.ps1 # interactive UCRT64 shell in the checkout
```

The Windows build uses the selected C++ compiler's builtin-header directory.
Keep Clang and `llvm-config` on the same major version, and rebuild PAL after
moving or changing the toolchain. The MSYS2 packages must provide the shared
`clang-cpp` library; the versioned, static-only LLVM packages are not substitutes.
Linux continues to use its existing resource discovery and setup.

### Build & verify

```bash
make                    # Rust binary + Pulse support library
make test -j8           # translate every test case, verify with F*
cd test/swap && make                       # one test
cargo run -- --print-ir test/swap/swap.c   # just the IR
```

PAL emits code against the [Palow](palow.md) memory model.

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
      --include <FILE>   preinclude a header (repeatable, in order)
      --only-function <NAME>  select a function body (repeatable)
      --print-ir         print IR and exit
      --time-passes      show per-pass timing
  -q, --quiet            suppress diagnostics on stderr
      --tmpdir <DIR>     directory for intermediates
```

Without `--only-function`, all input function bodies are translated. With it,
every selected name must have a definition; excluded bodies are reported as
warnings and become external declarations, not verified implementations.
Selected bodies still undergo the normal strict translation checks. This lets
a verification build check an actual dependency implementation with an
annotation header supplied by `--include`, without copying its C body.
Preincluded headers follow any platform headers in the compilation database.
A selected definition in an included header remains a proof root even when
none of the input sources call it.

---

## Reviewing pull requests

Changes to the translator are easiest to judge by looking at the F\* code they
produce. Every pull request therefore gets an automatic comment showing a diff
of the output `pal` generates for the whole test suite, base versus head. The
full diff is also attached to the workflow run as the `pal-output-diff`
artifact.

Comment `!diff` on a pull request to regenerate the report on demand; the
"PR Output Diff" workflow can also be started manually from the Actions tab
for any pull request number. On-demand reports take a few minutes, since the
command waits for the run it started before posting.

The workflows live in [`.github/workflows/`](.github/workflows):
`pr-output-diff.yml` builds both revisions and computes the diff (via
[`.github/scripts/pal-snapshot.sh`](.github/scripts/pal-snapshot.sh)),
`pr-output-diff-comment.yml` posts it, and `pr-output-diff-command.yml`
handles the `!diff` command. Configure a `PAL_GIST_TOKEN` repository secret
(a token with the `gist` scope) to additionally publish each full diff as a
gist; without it the comment links to the artifact instead.

---

## Documentation

Detailed references live in [`doc/`](doc/):

| Document | Covers |
|----------|--------|
| [Surface syntax](doc/pal_surface_syntax.md) | Full annotation reference: contracts, ownership, refinements, ghost code, Pulse interop |
| [Palow](palow.md) | The memory model: design, how C data is represented, implementation log |
| [Internals](doc/internals.md) | Pipeline passes, IR design, Zngur FFI, diagnostics, output structure, Pulse support library |
| [doc/README.md](doc/README.md) | Documentation index: how to write specs, how C data is modeled in Pulse |

---

## License

[Apache 2.0](LICENSE)
