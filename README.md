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
| F\*/Pulse | nightly 2026-10-14 | verifies generated `.fst` output |

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
cargo clippy --all-targets --all-features -- -D warnings
cargo fmt --check
LIBCLANG_PATH="$(llvm-config --libdir)" cargo test --all-features
cd test/swap && make                       # one test
cargo run -- --print-ir test/swap/swap.c   # just the IR
```

82 test directories, each a C file that PAL translates and F\*/Pulse
verifies. Create a new one with `./test/new.sh my_test`.

Clippy checks handwritten code without warnings; only four style lints are
exempted inside Zngur's generated FFI module (`src/clang.rs`).

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

### Optional MCP server

Requires Rust 1.88+, matching Clang/libclang 20+, and the verified Pulse support
library. The default build and ordinary translation CLI do not enable MCP.

```bash
env -u ADMIT -u OTHERFLAGS make -C pulse
cargo build --features mcp
LIBCLANG_PATH=/usr/lib/llvm20/lib target/debug/pal mcp
```

`pal mcp` uses stdio exclusively for MCP JSON-RPC; compiler/verifier logs go to
stderr. Options: `--fstar-exe` (default `fstar.exe`) and
`--pulse-dir` (default the build-time repository's `pulse/`, override after
relocating the executable). LLVM's selected Clang and loaded libclang must have
the same major version; a mismatch reports how to set `LIBCLANG_PATH`.

Open a session with `{"action":"open","root":"/path/to/project"}`. There is no
default project or `--root` argument. Absolute and relative directory paths are
accepted; relative roots resolve against the server process's working directory.
Invalid roots fail with `invalid_path` without disturbing the current project.
Opening the same canonical root preserves existing sessions and caches; opening
a different root cancels and joins old jobs, removes all old sessions/status
resources, ends their subscriptions, and clears verification caches. Old session
IDs are never reused. To clear caches without changing roots, use
`add_include_paths` with an empty list.

| Tool | Arguments and behavior |
|------|------------------------|
| `pal_session` | `{"action":"open","root":"/path/to/project","include_paths":[],"defines":[],"heartbeat":5}` returns the canonical `root`, a session ID, revision `0`, and status URI. Optional `heartbeat` sets the server-wide status interval in seconds. `cancel` takes `session_id`/`job_id`; `close` takes `session_id` and releases its snapshots. |
| `add_include_paths` | `{"session_id":"s1","include_paths":["include","vendor/include"]}` appends directories, like `-Iinclude -Ivendor/include`. Relative paths resolve against the server root. |
| `add_preprocessor_definition` | `{"session_id":"s1","defines":["FOO","BAR=value"]}` appends definitions, like `-DFOO -DBAR=value`. |
| `pal_verify` | `{"session_id":"s1","base_revision":0,"changes":[{"op":"reference","path":"examples/example.c"}]}` immediately reserves a background job. Stale revisions and busy sessions start no job. |
| `pal_query` | Takes `session_id`, optional `job_id`, and a tagged `query`: `symbols` with `path`; or `definition`, `references`, `callers`, `callees`, `hover` with `path` and zero-based UTF-16 `position`. References optionally include `include_declaration`. |

Both add tools preserve order and duplicates, including existing session options;
later definitions take precedence. Pass paths/definitions without `-I`/`-D` prefixes.
They return the session ID, unchanged accepted revision, and the full `include_paths`
(resolved paths) and `defines` lists. Updates apply to the next `pal_verify`, including
an empty-change refresh; accepted proofs/navigation remain unchanged until it succeeds.
Updates while a job is active fail with `session_busy`; closed/unknown sessions fail
with `unknown_session`. NUL-containing inputs reject the entire addition.
Every successful add call, including an empty list or unused option, invalidates
all server-wide exact-result entries and disables reuse of previously accepted
generated checked artifacts across sessions. The next verification starts with
an empty generated-proof cache even if emitted code is unchanged; subsequent
submissions can cache the new result normally. Failed/cancelled verification
does not restore invalidated entries, and in-flight jobs cannot revive them.
Installed F*/Pulse library caches are unaffected. Rejected add calls do not
invalidate caches.

The server publishes the `pal://sessions/{session_id}/status` resource template
at connect time, before any session exists, so generic MCP clients can route
status reads without refreshing their resource inventory.

Open a session, listen for its `pal://sessions/<id>/status` resource, wait for
the subscription acknowledgment, then submit verification. Use modern
`subscriptions/listen` with `notifications.resourceSubscriptions: [status_uri]`;
each `notifications/resources/updated` carries its subscription request ID.
Read the resource for the latest phase, elapsed time, diagnostics and error.
Polling `resources/read` also works; updates may coalesce. RMCP's 2026-07-28
protocol uses per-request `_meta` with `io.modelcontextprotocol/protocolVersion`
set to `2026-07-28` and `io.modelcontextprotocol/clientCapabilities` set to `{}`.
An older `initialize` handshake alone does not select modern subscriptions.

For unsolicited status reports, open with `"heartbeat":5`. The server sends one
`notifications/pal/status` custom notification per open session every five seconds,
starting after the first interval, including idle, queued and terminal sessions.
No resource subscription or progress token is required. Clients must handle this
notification method; generic clients may ignore custom notifications.
Its `params` is the same JSON status object returned by `resources/read`, including
`session_id`, `job_id`, revisions, phase, live `elapsed_ms`, message, diagnostics
and error. For example, during an isolated implementation proof:

```json
{"jsonrpc":"2.0","method":"notifications/pal/status","params":{"session_id":"s1","job_id":"j1","base_revision":0,"accepted_revision":0,"sequence":22,"phase":"verifying","elapsed_ms":23076,"message":"verifying proof units: Func_swap.fst","current_function":"swap","verification_cache_hit":false,"diagnostics":{},"error":null}}
```

`current_function` comes from PAL's validated C declaration metadata and remains
present while that function's F* subprocess runs, even when it produces no output.
It is absent during translation, multi-unit signature batches, cache validation,
and terminal/idle states; batch-start messages name the proof units instead.

Heartbeat seconds must be a nonnegative whole number within the platform timer
range. `0` disables reports server-wide; omission (or `null`) preserves the current
setting, initially disabled. A successful open with a new value replaces the timer;
invalid opens change nothing. The setting survives root changes and closing all
sessions, but removed/closing sessions are no longer reported. An already queued
notification can still arrive after close/reset/disable. Disconnect/shutdown stops
the timer. Existing resource subscriptions and their coalesced updates are unchanged.

Changes are tagged `reference` (attach/refresh a local file), `replace` (complete
inline `code`), or `append` (append `code` bytes exactly to a managed source,
without inserting a newline). Paths must be root-relative `.c`/`.h` paths;
absolute paths, traversal and escaping symlinks are rejected. Headers are include
overlays, not standalone translation units. References and implicit project
headers refresh on each submission; `changes: []` refreshes existing roots.
Inputs changing during a job fail rather than silently publishing mixed bytes.
Submitted sources and generated files are never written into the user's tree.

Only successful verification advances the accepted revision. Failed/cancelled
candidates never become patch bases: resend a corrected append against the
accepted revision, or replace the complete file. Queries default to accepted
code; an explicit retained candidate job ID exposes its available index with
`complete:false`. Direct-call queries do not invent function-pointer targets.

Unchanged generated `.fst`/`.fsti` proofs reuse F*'s checked-artifact validation;
body-only edits preserve interface-only dependents. F* first batches interfaces
and modules without interfaces, then checks each implementation separately,
with `fly_deps=false`. This preserves interface abstraction and dependency
checked artifacts; no custom dependency graph or admit flags are used. Exact
generated snapshots additionally share a 32-entry LRU. Active accepted proofs
stay pinned independently of eviction; missing/corrupt required artifacts fail
with `proof_cache_lost`. Caches are process-local, not durable. Verification is
serialized to bound solver memory while queries/status remain responsive.

This is a trusted local compiler service, not an include-filesystem sandbox.
Run the real integration regression with:

```bash
LIBCLANG_PATH=/usr/lib/llvm20/lib cargo test --features mcp --test mcp -- --nocapture
```

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
| [Structs](doc/structs.md) | What PAL emits per `struct` and `union`: generated types, predicates, fold/unfold, field projections |
| [Internals](doc/internals.md) | Pipeline passes, IR design, Zngur FFI, diagnostics, output structure, Pulse support library |
| [doc/README.md](doc/README.md) | Documentation index: how to write specs, how C data is modeled in Pulse |

---

## License

[Apache 2.0](LICENSE)
