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
- Every source is preflighted before any source is changed. Each replacement
  uses a staged file and atomic rename. Extraction saves the overlay first.
  Handled write failures attempt rollback; failed rollback reports a saved
  recovery file. The whole batch is not crash-atomic. After interruption,
  applying the overlay restores stripped files and recognizes restored ones.

`--check` and successful application do **not** establish proof validity.
Run PAL verification again after changing the implementation or annotations.

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
wrapper discovery follows quoted relative includes between supplied files,
including cycles, without importing aliases from unrelated translation units.
It does not search compiler include paths, read unlisted headers, or perform
macro expansion. A wrapper with a runtime definition in another branch
remains a runtime macro. Annotation-only wrapper names must not also name C
declarations or be undefined in their include context; such cases are rejected
before writing rather than guessing which uses are annotations.

Expression annotations (`_assert`, `_ghost_stmt`, and their recognized
wrappers) become `((void)0)`. This is intentional ordinary-C scaffolding, not
a PAL annotation: it keeps empty controlled statements, comma expressions,
and `for` clauses well-formed. Applying restores the original invocation.
Other annotations are removed without reformatting surrounding text.

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
