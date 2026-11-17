# Annotation overlays

`pal_annotations` extracts PAL annotation invocations from C and header files
into a versioned TOML file, and applies that overlay later:

```sh
cargo build --bin pal_annotations
target/debug/pal_annotations --extract file1.c include/file2.h -o out.annotations
target/debug/pal_annotations --apply out.annotations --check
target/debug/pal_annotations --apply out.annotations
```

The default extraction output is `out.annotations`. Extraction modifies the
input sources in place and refuses to overwrite an existing overlay.
`--root DIR` sets the source root, defaulting to the current directory; input
source paths and paths recorded in the overlay are relative to that root.
The overlay argument and `-o` remain relative to the current directory.
Sources must resolve to regular files inside the root. Sources and paths must
be UTF-8.

Use `--extract --proofs-only` to retain declaration contracts, parameter and
type specifications, and standalone specification vocabulary (`_type`, `_let`,
and `_include_pulse`, including module bodies) inline.
This extracts ghost statements, assertions, loop annotations, attributes within
function bodies (including label joins), and proof statements in wrapper bodies.
Application remembers this selection and preserves the retained specifications.
Wrappers with runtime variants still retain those runtime uses.

`-I DIR` adds a root-relative search directory for quoted and angle includes
between explicitly supplied files. The directories are recorded in the overlay
and reused at application; unlisted headers never supply annotation aliases.

## Guarantees

- Extract/apply with no intervening edits restores the original source bytes,
  including comments, whitespace, line endings, and original macro spellings.
- The scanner covers inactive preprocessor branches without needing compiler
  flags or a successful C translation.
- Symlink inputs are resolved and deduplicated. Their targets are edited;
  symlinks remain symlinks, and source file permissions are preserved.
- `--check` performs the same applicability checks as apply without writing.
  Success, including already-applied overlays, exits with status 0. Conflicts,
  invalid overlays, and I/O errors exit with a nonzero status.
- Reapplying an already-applied overlay does not duplicate annotations.
- Applying validates that only recognized annotations and their scaffolding
  change. This preservation check is mandatory, including for `--check` and
  exact-hash matches; a sidecar cannot authorize arbitrary C replacements.
- Every source is preflighted before any source is changed. Each replacement
  uses a staged file and atomic rename. Extraction saves the overlay first.
  Handled write failures attempt rollback; failed rollback reports a saved
  recovery file. The whole batch is not crash-atomic. After interruption,
  applying the overlay restores stripped files and recognizes restored ones.

`--check` and successful application do **not** establish proof validity.
Run PAL verification again after changing the implementation or annotations.

## Source-preserving application

Before any writes, application builds candidate files in memory and checks:

```text
erase_annotations(candidate) == erase_annotations(current_source)
```

`current_source` means the file immediately before application, normally the
unannotated source, including edits made since extraction. It is not the old
source identified by a stored digest. If annotations are already present, the
check compares the erased forms of both versions.

The check has three parts:

- Each payload must contain exactly one recognized annotation invocation,
  optional surrounding whitespace, and its semicolon when representing a
  compacted proof statement. Nested annotations remain inside that invocation.
  Appending ordinary statements, directives, or trailing comments is rejected.
  Only empty text and the known `((void)0)` placeholder are legal replacements;
  the replacement must agree with the annotation's erasure and matching tokens.
- Payloads must also be recognized at their actual insertion sites, not hidden
  in an existing comment/string or merged with neighboring tokens. Original
  bytes outside the insertion/placeholder spans are copied unchanged.
  Relocation may consume whitespace within a placeholder, but not user comments.
- Independent erasure compares the remaining C tokens, their preprocessor
  directive membership, and whether each `#define` is function-like. Thus
  moving tokens across a directive boundary, or changing `F(x)` into `F (x)`,
  is not mistaken for harmless formatting. The comparison normalizes trivia
  and complete standalone `((void)0);` scaffolding, never arbitrary expressions
  or controlled statement bodies.

The sidecar's wrapper table is not an authority for declaring runtime names to
be annotations. Wrappers are rederived from the candidate sources and their
actual include graph among files listed in the overlay. Every advertised
wrapper must match this classification; header candidates must themselves pass
the same preservation checks. Keep the header entries in an overlay even when
they have no annotations if they supply wrapper definitions.

Any failure rejects the entire batch, reports the affected file and the invalid
annotation or first unexpected difference, and leaves sources unchanged.
This is a syntactic annotation-erasure guarantee using PAL's recognized macro
conventions, not a proof of semantic equivalence under arbitrary macro expansion
or a validation of the proof annotations themselves. No compiler configuration
is needed, and inactive branches are checked too.

## What is extracted

The tool recognizes PAL's contract, refinement, ownership, loop, ghost,
and standalone Pulse helper macros. Nested invocations are captured as part
of the enclosing annotation, so `_requires(_inline_pulse(...))` is one record.
Comments, string literals, runtime `_container_of` uses, ordinary C `assert`,
and the Windows CRT's three-argument `_assert` are not annotation invocations.

PAL's own macro definitions remain infrastructure, including their
`C2PULSE`/ordinary-C branches. In other macro replacement bodies, annotation
invocations are extracted without deleting runtime C. Annotation-only wrapper
macros defined consistently in a source's include context are also recognized
at their use sites. Include all relevant headers in the extraction batch;
wrapper discovery follows quoted relative includes and the explicitly supplied
`-I` directories for quoted/angle includes, including cycles, without importing
aliases from unrelated translation units. It does not search implicit compiler
include paths, read unlisted headers, or perform
macro expansion. A wrapper with a runtime definition in another branch
remains a runtime macro. Annotation-only wrapper names must not also name C
declarations or be undefined in their include context; such cases are rejected
before writing rather than guessing which uses are annotations.
In proof-only mode, redefined (`#undef`) wrappers are conservatively retained,
including their aliases, rather than assuming their external definitions are
proof-only. Reusable `_inline_pulse` fragments in macro definitions remain
specification infrastructure.

Standalone proof statements inside a parsed compound statement are removed, together
with their semicolons and (when they occupy a whole line) indentation and line
ending. Expression annotations (`_assert`, `_ghost_stmt`, and their recognized
wrappers) in other positions become `((void)0)`. This ordinary-C scaffolding
keeps unbraced controlled bodies, comma expressions, and `for` clauses
well-formed. Blocks with parser errors (for example around conditional
preprocessing or opaque macros) conservatively retain these no-ops.
Applying restores the original text. Older overlays retain their
original no-op behavior; each file records the `compact_statements` mode.
Proof-only attribute lines (such as a loop invariant on its own line) are
removed in the same way. Other annotations are removed without reformatting
surrounding text.

## Format and matching

The format is TOML with `format_version = 1` and a `[[files]]` table per
distinct physical source. Each file records root-relative `path`, original
and stripped SHA-256 digests, optional wrapper macro descriptions, and
`[[files.annotations]]` records containing:

| Field | Meaning |
|---|---|
| `id` | Diagnostic identifier local to this extraction |
| `text` | Original annotation invocation, including its internal trivia |
| `replacement` | Empty text or ordinary-C scaffolding emitted by extraction |
| `offset` | Byte position used only when the stripped file digest matches |
| `owner` | Named C declaration kind/name and enclosing preprocessor context |
| `site` | Attachment category, required token windows, boundary constraints, and gap trivia |

Tree-sitter C identifies function definitions, declarations, typedefs, named
records/enums, and macro definitions in the stripped source. Standalone helper
annotations use the translation unit as owner. Unclassified or incomplete C
can also fall back to a translation-unit owner, with correspondingly more
conservative relocation.

For edited files, the owner must resolve uniquely and the required token
context must identify exactly one site within it. Whitespace and ordinary C
comments are ignored during token matching. Windows initially extend eight
tokens in each direction and expand during extraction if needed to
disambiguate a site. Boundary flags distinguish sites at owner boundaries.
No token window is silently relaxed during application; offsets and occurrence
numbers are never relocation fallbacks.

This survives changes elsewhere in a file, declaration reordering when local
context is unchanged, and many formatting changes. It deliberately reports
conflicts for renamed owners, ambiguous repeated declarations, or modifications
to required local context. Identical loop headers can be distinguished by
their required surrounding tokens; the tool never blindly selects the nth loop.
It does not infer that a relocated proof remains valid, rewrite names in Pulse
snippets, or automatically map renamed files.

To edit a sidecar's `text`, do so while the sources are stripped, then apply.
Existing inline annotations must match the overlay; conflicting annotations
are not overwritten or partially merged.

## Tests

```sh
make annotations-test
make test -j8
```

The Rust tests include real extract/check/apply CLI invocations over temporary
copies of every Git-tracked `.c` and `.h` file. They check byte-for-byte
restoration, symlink preservation, a second extraction finding no remaining
invocations, idempotent application, conflicts, and compilability of stripped
control-flow/`for`-clause fixtures. The repository checkout is never stripped by
the census.

Preservation regressions cover injected C/directives, forged replacement tokens
and wrapper metadata, payloads hidden inside comments, macro-definition spacing
and directive-boundary changes, preservation of comments in edited placeholders,
and valid source/proof edits. Both `--check` and `--apply` reject invalid
multi-file overlays without partially modifying any source.
