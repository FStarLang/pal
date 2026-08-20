# PR plan: upstreaming the C-project integration work

`nswamy/pal-c-project-integration` carries 55 commits accumulated while bringing PAL
up against a real C codebase. They are being upstreamed as 35 small PRs, each one a
self-contained change, almost all with their own regression test.

Every branch is cut from `origin/main` (or from the branch it depends on) and carries
only the commits for its own PR, so each PR reviews as the change it claims to be.
Each branch builds, passes `test/check-template.sh` and `cargo fmt --check` /
`clang-format --dry-run`, and verifies every test directory it touches.

One commit is **not** upstreamed: `c34b722 Pin the 2026-08-09 nightly`. `main` has
since moved to 2026-08-17, which is strictly newer, so the pin is already satisfied.
`32264e3 Restore the shared template symlinks in two test directories` is not a PR of
its own; it is folded into PR14 and PR15, which introduce the directories it repairs.

Six PRs carry no test directory of their own — PR08, PR09, PR10, PR19, PR31, PR32.
Four of those are enablers whose observable behaviour is what makes some *other* PR's
test verify (the dependency edges below say which), one is a `pulse/` library lemma,
and one is a `tests-todo` reproducer. Each was checked with a full `make test -j8`
rather than a targeted run.

Where review has found that an enabler could carry its own test after all, one has been
added: PR01 gained `test/extern_const` and PR05 gained `test/refinement_scoping`.

## Merge order

The edges below are real: a dependent PR either needs the parent's code to compile, or
its test does not verify without the parent's behaviour, or it needs the parent's test
fixture to exist. Anything not named as a dependency can be merged in any order.

```
  independent (base = main), 22 PRs:
  PR01  PR02  PR03  PR05  PR06  PR07  PR08  PR09  PR10  PR12  PR13
  PR14  PR15  PR16  PR17  PR18  PR19  PR20  PR22  PR25  PR31  PR32

  PR10 ──► PR30                    array lemmas ──► memset intrinsic

  PR18 ─┐
        ├─► PR21                   unreachable + switch shapes ──► arms that jump/abort
  PR20 ─┘

  PR05 ──► PR27 ──► PR28           refinement scoping ──► optional outputs ──► transfer

  PR28 ─┐
        ├─► PR11                   caller transfer + ABI sizes ──► core_ref out-cells
  PR13 ─┘

  PR22 ─┐
        ├─► PR23 ──► PR24          pointer/const typedefs ──► parameter modes
  PR28 ─┘

  PR28 ─┐
        ├─► PR29                   declining optional parameters
  PR23 ─┘

  PR25 ─┐
        ├─► PR26 ─┐
  PR28 ─┘         ├─► PR33         rewrites_to ──► inline-Pulse postconditions
  PR06 ───────────┘

  PR03 ─┐
        ├─► PR04a ─┐
  PR19 ─┘          ├─► PR04b ──► PR04c   pruning what a contract still names
  PR33 ────────────┘
```

Edge-by-edge, in words:

| Child | Parents | Why |
|---|---|---|
| PR04a | PR03, PR19 | its `enum_const_in_contract` test names enumerators in a contract (PR03) and switches on an enum-typed scrutinee (PR19) |
| PR04b | PR04a, PR33 | extends the same `prune.rs` scanner; its `verbatim_module_ref` test writes an inline-Pulse `_ensures` that determines the result (PR33) |
| PR04c | PR04b | extends `scan_verbatim_module_ref`, introduced by PR04b |
| PR11 | PR28, PR13 | reuses the caller-side ghost-step machinery (PR28); its test passes `sizeof(struct hdr)` to an `unsigned` parameter, which needs the ABI-pinned size to prove in range (PR13) |
| PR21 | PR18, PR20 | test fixture (PR18) and the switch lowering it extends (PR20) |
| PR23 | PR22, PR28 | pointer-typedef attributes (PR22); a `const`-through-typedef pointer that is also `_nullable` needs the reworked null guards (PR28) |
| PR24 | PR23 | refines the `const` parameter-mode decision PR23 introduces |
| PR26 | PR25, PR28 | struct-rvalue hoisting is what the `rewrites_to` form is for (PR25); its `nullable_out` regression needs PR28 |
| PR27 | PR05 | its test writes `_refine(*this == *Src)`, a refinement naming an earlier parameter |
| PR28 | PR27 | continues the same optional-output work |
| PR29 | PR28, PR23 | reworks PR28's null guards; `nullable_const_in` needs PR23's const-typedef handling |
| PR30 | PR10 | the `memset` translation discharges its proof with PR10's array lemmas |
| PR33 | PR26, PR06 | extends PR26's "does `E` mention the result" test; its fixture calls a `_pure` external declaration (PR06) |

Once a parent lands on `main`, rebase the child onto `main` before opening it, so the
PR diff shows only its own commits.

Suggested wave order, to keep the review queue shallow:

1. **Wave 1** — the 22 independent PRs, all reviewable in parallel.
2. **Wave 2** — PR04a, PR21, PR27, PR30.
3. **Wave 3** — PR28.
4. **Wave 4** — PR11, PR23, PR26.
5. **Wave 5** — PR24, PR29, PR33.
6. **Wave 6** — PR04b, then **Wave 7** — PR04c.

## The PRs

### Frontend robustness — accepting the C that real headers contain

| | |
|---|---|
| **PR01** | `nswamy/pal-pr01-header-robustness` |
| Commits | `8a8502e`, `1d53a75`, `e835866` |
| Depends on | — |

PAL compiles with `-DC2PULSE`, under which a project's annotation macros expand away
and a variable read only from inside an assertion looks written-but-never-read. A
compilation database carrying `-Wall -Werror` then aborts the translation unit over a
warning PAL caused itself; the suppressions go at the end of the argument list so a
`-Wall` from the database cannot re-enable them. Also skips two declaration kinds that
stopped translation outright: a stray `;` after a macro (clang `EmptyDecl`) and a
definition-less `extern struct attrs name;`, and names `FileScopeAsmDecl` explicitly.

A third commit, added during review, narrows that last one: an `extern const` object
has a real value fixed by another translation unit, so it is emitted as `assume val`
rather than dropped — the same treatment PR06 gives a `_pure` external function. It has
to be *assumed* rather than defined, because the global path fills a missing initializer
with the type's default; that is correct for a tentative definition (`T x;`, which C
zero-initializes) but would invent a value for an `extern const`. The new `is_external`
flag distinguishes the two. A non-const `extern T x;` is still dropped.

---

| | |
|---|---|
| **PR02** | `nswamy/pal-pr02-contract-lexer-literals` |
| Commits | `76f19bf` |
| Depends on | — |

The contract lexer took a character literal to be exactly one character, so an on-media
signature written `'hdIR'` could be *written* in C but not *specified*. Multi-character
constants now pack most-significant-first the way clang and MSVC agree to, sign-extended
at four characters because the type is `int`. Adds hexadecimal and octal constants in the
same pass — an on-media structure is documented in hex, so a specification about one
could otherwise only be written in a base its subject is not described in.

---

| | |
|---|---|
| **PR03** | `nswamy/pal-pr03-enum-constants-in-contracts` |
| Commits | `ea81be6`, `abca233` |
| Depends on | — |

Clang inlines an enumerator as an integer literal in a *body*, but contracts are raw
source snippets PAL parses itself, so an enumerator in a `_requires` was an unresolved
name and contracts had to repeat its value as a magic number. Publishes each enumerator
as a pure global constant; existing name resolution, emission and pruning do the rest,
so an enum reached through a header costs nothing.

`abca233` (added in review) stops an enumerator from being given an address. Routing it
through the ordinary global path also emitted the storage a global has — an assumed
address, a non-null axiom and an acquire — but an enumerator is a C *constant*, not an
object: it has no storage and `&Color_Red` cannot be written, so nothing translated
could ever mention that pointer. Gating the address on a new `is_enum_constant` flag, in
`emit` and in `Env::addressable_global` alike, takes an enumerator from eighteen emitted
lines to six.

---

| | |
|---|---|
| **PR04a** | `nswamy/pal-pr04a-prune-enum-constants` |
| Commits | `3b88a43` |
| Depends on | **PR03**, **PR19** |

The pruner drops declarations that are not from the main file, and it only kept what it
could see referenced. A bare variable reference in a contract recorded nothing, so an
enumerator a contract still names was pruned away and the generated module referred to a
constant that no longer existed. The scan now records a global-variable dependency for it,
which over-approximates in the safe direction.

---

| | |
|---|---|
| **PR04b** | `nswamy/pal-pr04b-prune-verbatim-module-ref` |
| Commits | `380f5b2` |
| Depends on | **PR04a**, **PR33** |

The same scan skipped the verbatim tokens *between* an inline-Pulse annotation's
antiquotes, so a generated module named directly in contract text — `Func_parity.parity`,
say — was not a dependency and got pruned. The verbatim text is opaque, so the referenced
declaration is recovered from the module name, which `emit::module_name_for_decl` builds by
prefixing the C name. A segment that names no module simply matches no declaration.
This commit also converts the `enum_const_in_contract` fixture's copied scaffolding to the
shared template symlinks.

---

| | |
|---|---|
| **PR04c** | `nswamy/pal-pr04c-prune-shared-include` |
| Commits | `3f9ec87` |
| Depends on | **PR04b** |

An `_include_pulse` module was keyed by its source location, so shared proof vocabulary had
to be written out in full at each use. Keying it by module name instead lets the vocabulary
live in a header and be used from several translation units. An INCLUDES module is referred
to by its bare name, with no prefix to recognize it by, so every verbatim segment has to be
offered as a candidate.

---

| | |
|---|---|
| **PR05** | `nswamy/pal-pr05-refinement-scoping` |
| Commits | `60e9210`, `f1ded6e`, `0f60a13` |
| Depends on | — |

A `_refine` on one parameter could not mention another, because the type pre-pass
elaborated every parameter in the environment the function started with; each parameter
is now pushed as its type is elaborated, which is the order C itself gives them.
Separately, `_Use_decl_annotations_` gives a definition the declaration's annotations,
and merge already mapped declaration parameter names onto definition names for
`_requires`/`_ensures` but not for refinements inside argument types. The scope check
also moves to after merge, which is the first point at which the two are reconciled.

---

| | |
|---|---|
| **PR06** | `nswamy/pal-pr06-pure-external-decls` |
| Commits | `cddb926` |
| Depends on | — |

A `_pure` function *with* a body is an F* `let`; one without fell through to the
ordinary external-declaration path and became a stateful `fn`, which Pulse rejects in a
spec with "cannot use ... in impure spec". Emits them as `assume val`, sharing signature
elaboration with the defined case so both forms agree on parameters, the `Pure` wrapper
and contract placement. Call sites are unchanged.

### Integers and literals

| | |
|---|---|
| **PR07** | `nswamy/pal-pr07-integer-literal-casts` |
| Commits | `9f5c474`, `d1e32c4`, `a207b96`, `6668b8a` |
| Depends on | — |

Generated interfaces define fixed-width bit-pattern constants as casts from long
literals. On LP64 a high-bit long is a signed 64-bit value, and emitting the source
literal followed by `Int.Cast.int64_to_int32` left F* with an out-of-range conversion.
Adds a post-elaboration `normalize_casts` pass that recovers the mathematical value,
preserves representable casts as explicit `Int.Cast` operations, and rewrites only
out-of-range ones to target-typed literals. The three follow-ups make emission agree
with it: one shared `machine_int_literal` table for expressions *and* patterns (the
constructor form is not interchangeable — its refinement needs SMT, and Pulse typechecks
candidate witnesses without it), and parentheses around negative literals, which F*
otherwise lexes as infix subtraction (`=-` and `:=-` are single operators).

---

| | |
|---|---|
| **PR08** | `nswamy/pal-pr08-integer-conversions` |
| Commits | `904669d` |
| Depends on | — |

A narrowing cast out of `size_t` emitted `UIntN.uint_to_t (SizeT.v x)`, whose refinement
is not provable for an opaque `c_sizeof`: `FStar.SizeT` bounds `fits` from below only.
Emits the total `sizet_to_uint32`/`sizet_to_uint64` instead, whose postcondition
`v y == v x % pow2 N` is exactly C's conversion rule. Also gives a spec integer standing
in a separation-logic position the C reading it deserves — `with_pure (v <> 0)` — since
assertion bodies are C-preprocessed and a source `false` arrives as the literal `0`.

### Pulse support library

| | |
|---|---|
| **PR09** | `nswamy/pal-pr09-opaque-string-literals` |
| Commits | `feb28f6` |
| Depends on | — |

The trusted static-literal model exposes only a borrowed address — no contents, length
or ownership — so the full array specification built at every decay site was unused.
Making the primitive depend only on the inferred element type keeps the abstraction and
stops large string-heavy switches from generating thousands of irrelevant
character-conversion proof obligations.

---

| | |
|---|---|
| **PR10** | `nswamy/pal-pr10-array-init-lemmas` |
| Commits | `72d3a82` |
| Depends on | — |

`array_spec_initd`, `array_spec_mask` and `array_spec_len` are all abstract, so a client
holding `array_spec_initd s i` could not conclude `i < len` or `array_spec_mask s i`,
both of which hold in the implementation. That is the position a caller of
`array_return_cell` is in.

---

| | |
|---|---|
| **PR30** | `nswamy/pal-pr30-memset-wrapper` |
| Commits | `17a2454`, `a906963` |
| Depends on | **PR10** |

Real code calls a platform zeroing wrapper — `RtlZeroMemory`, `bzero`, a project's own —
which takes `(destination, size)` and defeats the `memset` recognizer, so the call became
an uninterpreted stub and nothing in the signature related the `void *` back to the
object being zeroed. `_memset_zero` marks such a declaration; `f(ptr, sizeof(*ptr))` and
`f(arr, N)` (with the extent checked against the array's own type, not trusted) translate
exactly as a direct `memset` does, and any other shape is a diagnostic rather than a
fallback to the stub the marker exists to avoid. `Pulse.Lib.C.Array.memset` also drops its
`array_spec_full` requirement — storage under construction cannot satisfy it — to
`array_spec_full_mask`, writing cells with `array_write` instead of `fill`.

### Types, layout and declarations

| | |
|---|---|
| **PR12** | `nswamy/pal-pr12-mutually-recursive-types` |
| Commits | `451d605` |
| Depends on | — |

A cycle among C types is both an F* module cycle and an ill-founded ownership predicate.
F* reports it as `Error 308` from dependency analysis over the whole translation unit, so
a single recursive type reachable from a third-party header took every other module down
with it — and, because the failure was in `--dep`, a subsequent `make` ran off a partial
`.depend` and silently skipped most of the work. A new merge phase builds the definitional
dependency graph (descending into function-pointer signatures, which the emission-order
graph did not) and demotes a pointer to `core_ref` exactly when its pointee can reach back
to the declaration containing it, recomputing after each removal. Self-references are left
alone; a cycle no pointer can break is reported rather than handed to F*.

---

| | |
|---|---|
| **PR13** | `nswamy/pal-pr13-sizeof-abi` |
| Commits | `7973441` |
| Depends on | — |

`sizeof(T)` committed to no particular value, so any arithmetic over sizes was unbounded.
Carries clang's ABI size on the record definition and emits it, in the record's own
module, as a refinement-typed constant that `sizeof` sites refer to. Introducing the size
once *on the type* is what keeps this sound — stating it at each site would let two sites
claim different sizes. A refinement-typed constant rather than an `SMTPat` lemma, because
a trigger for a ground fact contains no variable. Non-record types still size opaquely.

---

| | |
|---|---|
| **PR14** | `nswamy/pal-pr14-offsetof` |
| Commits | `b0cdb21` |
| Depends on | — |

`offsetof(S, m)` reached the unsupported-rvalue fallthrough, which loses the whole
enclosing function — and the functions that use it are the back-patching writers that go
back and fill in a length or checksum. Folded through `EvaluateAsInt`, sharing the
assumption `c_sizeof` already makes. (The test fixture's template files are symlinked, as
`test/check-template.sh` requires; the integration branch fixed that in a later commit.)

---

| | |
|---|---|
| **PR15** | `nswamy/pal-pr15-initializer-lists` |
| Commits | `66aad8b`, `9b17319` |
| Depends on | — |

C11 6.7.9p21 zero-initializes the elements an initializer list does not reach, but the
translation built an array literal with exactly as many elements as the list had, so
`uint8_t bytes[16] = {0}` produced a `uint8_t[1]`. That made `T x = {0}` untranslatable
for any aggregate containing an array — the common way to declare a zeroed GUID, key or
digest — and failed badly, since the `admit()` placeholder is not valid Pulse in an
expression position. Zeroes are now built structurally, so padding an array of arrays
yields zeroed inner arrays. The second commit accepts `int x = {0}` and `T x = {}`, which
is how an initializer is written against a typedef that is a struct on one platform and an
integer on another. (Template files symlinked, as above.)

---

| | |
|---|---|
| **PR16** | `nswamy/pal-pr16-local-address-not-null` |
| Commits | `0e09975` |
| Depends on | — |

A local's address is never NULL in C, but the cell a local becomes is an ordinary `ref`,
and `ref` includes `null` — so a callee whose contract says its out-parameter is non-null
was uncallable on `&local` unless the caller established it at every call. Said once, at
the declaration; the conclusion is pure, so it stays in scope for the rest of the body.

### Diagnostics

| | |
|---|---|
| **PR17** | `nswamy/pal-pr17-goto-label-diagnostics` |
| Commits | `343d8da` |
| Depends on | — |

Pulse has no syntax for an unannotated label followed by more code, so a `goto` target
needs an explicit `_ensures`. Emitting the label anyway produced a module that did not
parse, and F* pointed at the enclosing function rather than at the label. Reported during
translation instead. Adds a diagnostic test kind for cases where PAL is expected to reject
its input and there is nothing to verify: the test symlinks `_templates/Makefile.diagnostic`
and lists the required messages, optionally pinned to a source location, in
`expected-diagnostics.txt`. `test/new.sh -d` scaffolds one.

### Switches and unreachable code

| | |
|---|---|
| **PR18** | `nswamy/pal-pr18-unreachable` |
| Commits | `09b6b9e`, `a88a3cd` |
| Depends on | — |

`_assert(false)` in a dead `default:` arm is a claim that control never reaches there, not
a proposition to carry forward; emitting `assert (with_pure (0 <> 0))` left the arm's own
footprint in the enclosing join, which then came out as an irreducible `match` on the
scrutinee — making an unreachable arm the reason a proof failed. Recognizes a statically
false condition through casts and emits `unreachable ()`, whose postcondition `pure False`
absorbs whatever the join needs. `__builtin_unreachable` — how a noreturn abort is spelled
to the C compiler, and required for a dead default arm to compile at all — is rewritten to
the same thing. The claim is discharged, never assumed.

---

| | |
|---|---|
| **PR19** | `nswamy/pal-pr19-switch-enum-scrutinee` |
| Commits | `588982d` |
| Depends on | — |

Clang promotes a switch condition, and an enumeration modeled by its underlying integer
type makes that promotion the identity, which the rvalue translation elides — but the
scrutinee binding was still annotated with the promoted type, so the declared type and the
bound value were syntactically distinct and Pulse's dereference tactic, which compares
syntactically, rejected the binding. Other promotions are genuine casts and keep their
promoted type.

---

| | |
|---|---|
| **PR20** | `nswamy/pal-pr20-switch-default-and-if-chain` |
| Commits | `12f46ba`, `59600ae` |
| Depends on | — |

Consecutive labels *nest* in clang, so `case 2: case 3: default:` arrives as
`CaseStmt(2, CaseStmt(3, DefaultStmt(..)))`; the group builder peeled only the `CaseStmt`
chain and statement translation then rejected the stray `DefaultStmt`. Peels the whole
chain in either order and marks the group default, dropping its explicit case values —
an arm reached by anything gains nothing from also testing for 2 or 3. The second commit
lowers a fall-through-free switch with a `default` as an if/else chain: the general
encoding threads `hit`/`brk` flags, so every arm executes under a compound condition over
mutable state, and the join — phrased in terms of the scrutinee — never meets the guards.
An explicit switch postcondition still takes the match form, which needs one.

---

| | |
|---|---|
| **PR21** | `nswamy/pal-pr21-switch-jump-abort` |
| Commits | `f9e2cdf`, `459eb94` |
| Depends on | **PR18** (test fixture), **PR20** (switch lowering) |

The ordinary shape of a version dispatcher: two live arms and a default that raises a
fatal error and jumps to the function's single exit. An arm was taken to have no
fall-through only when it ended in a direct `break`, so an arm leaving by `return`, by a
`goto` out of the switch, or by a noreturn abort forced the general encoding. All three
are now admitted; `abortsControlFlow` propagates the claim the way control flow does (a
block aborts if any statement does, a `do-while(0)` wrapper if its body does, an `if` if
both arms do or its condition folds). This also needs the goto restructuring to look
inside match branches, which it did not. Separately, `do { ... } while (0)` is not a
loop — it is the single-statement-body idiom — and encoding it as one lost everything the
body established, including the claim that it cannot be reached at all.

---

| | |
|---|---|
| **PR31** | `nswamy/pal-pr31-annotated-tail-conditional` |
| Commits | `6578d2a` |
| Depends on | — |

Pulse rejects an annotated conditional in tail position: the annotation and the enclosing
signature's postcondition are two postconditions for the same term. Sequencing a unit after
it keeps the annotation local to the join, which is the only place it constrains anything.

### Pointer kinds, `const` and parameter modes

| | |
|---|---|
| **PR22** | `nswamy/pal-pr22-pointer-typedef-attrs` |
| Commits | `79e421e`, `1a40b52` |
| Depends on | — |

`_array`, `_arrayptr` and `_core_ref` were applied to the translated type as written, so a
parameter declared with a pointer typedef (`typedef E* PE; ... _array PE table`) translates
to an opaque type reference and the attribute had nothing to attach to — PAL warned
"`_array` on non-pointer type" and then failed to index the table. Desugars a declared type
that resolves to a pointer before applying a pointer-kind attribute, and threads the
declared type through the remaining `trTypeAttrs` call sites. This is what a codebase that
names every pointer with a `P`-prefixed typedef needs.

---

| | |
|---|---|
| **PR23** | `nswamy/pal-pr23-const-typedef` |
| Commits | `5ee9c3a` |
| Depends on | **PR22**, **PR28** |

`ParamMode` inference used `dyn_cast<PointerType>`, which does not desugar, so a parameter
declared `PCT` for `typedef const T *PCT` read as an ordinary mutable input and a caller
lost its hold on the value it passed in. `getAs<PointerType>()` desugars. That contract
cannot be used under a null guard, though — `unless_null p X` collapses to `emp` at a
literal-null call site, leaving the implicits unsolvable — and inferring `Regular` for every
`_nullable` parameter would cost precision an optional input can otherwise keep. So the
choice belongs to the declaration: a new `_mutable` annotation asks for the quantified
treatment.

---

| | |
|---|---|
| **PR24** | `nswamy/pal-pr24-const-param-modes` |
| Commits | `74eca11` |
| Depends on | **PR23** |

A `const` parameter is translated as a borrow, which only works when it has ownership to
speak of. Two kinds do not, and for them the permission implicit occurs nowhere but in
`emp`, so nothing at a call site can solve it and the call does not elaborate — reported
as unresolved uvars, a long way from the C that caused it. A scalar passed by value: the
qualifier is about the callee's local, not the caller's storage, so top-level `const` is
now a borrow only when the canonical type is a pointer. And a `_core_ref`: an axiomatized
address whose predicate is `emp` by construction, now always regular, whether written on
the declaration or reached through the typedef chain — which is where it has to be written
to land on the pointee of a `void const **`.

### Structure rvalues and result-determining contracts

| | |
|---|---|
| **PR25** | `nswamy/pal-pr25-rvalue-member` |
| Commits | `359cad5`, `eecb520`, `05e1707` |
| Depends on | — |

`f(x).field` and `(struct s){...}.field` are rvalues: the base is a prvalue structure, so
there is no lvalue to project from and `trRValue` reported "unsupported rvalue expression
MemberExpr". Translates the base as a value and projects the field out of it. The call
result then has to live somewhere: Pulse hoists it on its own, but its hoisted binders are
named from a counter that does not survive leaving a statement, so two can share a name and
an existential close at a conditional's join captures the wrong one — demonstrably, since
giving the two calls different return types still projects the closed binder at the other
call's field. Binds the result to a PAL-level local instead, named from a function-wide
counter, and only in unconditionally evaluated positions (moving a call out of a `?:` arm
would evaluate it when C would not). The third commit handles a compound literal, which
C11 6.5.2.5p4 makes an lvalue — the object it names is unnamed and fresh, so translating
it as its own value loses nothing.

---

| | |
|---|---|
| **PR26** | `nswamy/pal-pr26-rewrites-to` |
| Commits | `97ab222` |
| Depends on | **PR25** (test fixture and the hoisting it relies on), **PR28** |

`_ensures(return == E)` with `E` free of `return` fixes the result outright, and Pulse has
a better form for exactly that: `rewrites_to`, read as a substitution. That is what a
conditional needs — a call inside a branch binds its result to a branch-local name, the
branch's postcondition closes over it existentially, and Pulse's join gives up on an
`exists*`, leaving a `match` on the guard that nothing afterwards can take a resource out
of. With `rewrites_to` the local never reaches the postcondition.

---

| | |
|---|---|
| **PR33** | `nswamy/pal-pr33-inline-pulse-ensures` |
| Commits | `7ddb7ed` |
| Depends on | **PR26**, **PR06** |

Extends PR26's "does `E` mention the result" test to look inside an inline-Pulse fragment's
antiquotations, which is both sufficient and precise — that is the only way an inline
fragment can reach the result. It is also the only way to say "this function decides that
predicate", which the impure-spec elaborator needs a `rewrites_to` for. The fixture calls a
`_pure` external declaration, hence PR06.

### Optional (`_nullable`) parameters

| | |
|---|---|
| **PR27** | `nswamy/pal-pr27-nullable-out` |
| Commits | `f6e105b`, `c1c8f8d` |
| Depends on | **PR05** (its test refines one parameter against another) |

An `_Out_opt_` parameter is a pointer the caller may pass as NULL and the callee writes
through only after testing it. The existential for the pointee now lives *inside*
`unless_null`, so the null branch does not have to name a value that is not there; the
intro and elim rules are stated per pointer flavor rather than through the typeclass, so
no `has_is_null` constraint is left unsolved; and the null test eliminates the guard on
entry to each branch. Pulse cannot discharge the slprop it infers when joining two
branches, so each branch restates the guarded resource on the way out — as an `assert`,
because a pointer's value is only resolved against the context in a slprop position.
Branches that return, break, continue or jump need no restatement and would be wrong to
receive one. The second commit does the same for the *other* conjunct that fails to match:
a borrowed structure the branch reads through, where reading a member splits the parameter
into per-member ownership. Splitting `Nullable` into an interface keeps `unless_null`
abstract.

---

| | |
|---|---|
| **PR28** | `nswamy/pal-pr28-nullable-caller-transfer` |
| Commits | `c2065fb`, `ffe5256` |
| Depends on | **PR27** |

A callee states its half of the bargain under a guard, which is right for the callee and
wrong for its caller — which knows which side of the test its own argument is on and wants
the resource, or nothing, rather than a guarded maybe. Until now a caller that supplied an
optional output never got the storage back, and one that declined was told it had leaked a
resource that was never there. Declining is easy; supplying takes a *fact* — eliminating
the guard needs to know the pointer is not null, and the only evidence is the resource now
inside it — so the fact is established before the call and carried across as a pure
proposition, with the lemma chosen by the callee's parameter mode. Two arguments that look
identical are distinguished: ownership PAL emitted may be taken back, ownership written by
hand in the enclosing contract (a `_nullable` or `_plain` argument) may not. The first
commit fixes the name the preserved payload is given, which has to be the one the signature
will accept.

---

| | |
|---|---|
| **PR29** | `nswamy/pal-pr29-nullable-decline` |
| Commits | `eca2b11`, `f58d84b` |
| Depends on | **PR28**, **PR23** |

A call declining several `_nullable` outputs passed the same `NULL` for each, so the guards
differed only in the resource they carry — which is exactly the implicit `elim_null_ref`
must recover by matching. With more than one in scope the match is ambiguous and the whole
thing surfaces as "Could not solve typeclass constraint `has_is_null`", naming a typeclass
that appears nowhere in the C. Splits the guards at the *pointer* instead: `null_ref`
returns a null pointer bound to a name, one per declined output. The second commit lets a
call site decline an optional *const* input, whose guarded resource names the permission
and pointee the caller handed in; a declining caller holds nothing to solve those against,
so the guard — `emp`, the pointer being null — is written down at the call site with no
metavariables left in it. Callers previously worked around this by declaring such
parameters mutable, which locks out any caller holding only a fraction of the argument.

### `core_ref` out-cells

| | |
|---|---|
| **PR11** | `nswamy/pal-pr11-core-ref-out-cell` |
| Commits | `2640b37`, `d677cee`, `068411a` |
| Depends on | **PR28** (reuses the caller-side ghost-step machinery), **PR13** |

`f((void const **)&typedLocal)` is how every acquire-a-buffer interface is spelled; the
cast was dropped and a `ref (ref T)` reached a `ref core_ref` parameter, which is
ill-typed. `ref_to_core` erases the type of a pointer *value* and says nothing about the
slot that holds one, so `core_cell` is added for that view, with the shifts that move
ownership across it — asymmetric, because an out-parameter goes in empty and comes back
full, and accepting either an uninitialized slot or one just set to NULL. Casts are
stripped before the argument's type is inferred, or inference reports the type the cast
asks for and the shift is never emitted. What the acquired buffer *means* is still the
contract's business.

### Not a fix

| | |
|---|---|
| **PR32** | `nswamy/pal-pr32-todo-reproducer` |
| Commits | `e8f22b7` |
| Depends on | — |

A reproducer under `examples/tests-todo/`, no product change. A struct's deep predicate is
indexed by the whole struct value but owns only what its pointer members point at, so
writing any other member moves the index without changing the ownership; the stale chunk
is what the prover matches first, and the failure is reported as an inexplicable
inequality of two `pts_to` terms. The reproducer narrows the trigger to a single pointer
member: with it the file fails, and deleting it — keeping the union, the nesting and the
write — makes the identical file verify. The fix is to index the predicate by the
ownership-relevant projection of the struct rather than the whole value.

## Branch index

Each branch below is checked out at the merge of its bases plus its own commits.

| PR | Branch | Cut from |
|---|---|---|
| PR01 | `nswamy/pal-pr01-header-robustness` | `main` |
| PR02 | `nswamy/pal-pr02-contract-lexer-literals` | `main` |
| PR03 | `nswamy/pal-pr03-enum-constants-in-contracts` | `main` |
| PR04a | `nswamy/pal-pr04a-prune-enum-constants` | PR03 + PR19 |
| PR04b | `nswamy/pal-pr04b-prune-verbatim-module-ref` | PR04a + PR33 |
| PR04c | `nswamy/pal-pr04c-prune-shared-include` | PR04b |
| PR05 | `nswamy/pal-pr05-refinement-scoping` | `main` |
| PR06 | `nswamy/pal-pr06-pure-external-decls` | `main` |
| PR07 | `nswamy/pal-pr07-integer-literal-casts` | `main` |
| PR08 | `nswamy/pal-pr08-integer-conversions` | `main` |
| PR09 | `nswamy/pal-pr09-opaque-string-literals` | `main` |
| PR10 | `nswamy/pal-pr10-array-init-lemmas` | `main` |
| PR11 | `nswamy/pal-pr11-core-ref-out-cell` | PR28 + PR13 |
| PR12 | `nswamy/pal-pr12-mutually-recursive-types` | `main` |
| PR13 | `nswamy/pal-pr13-sizeof-abi` | `main` |
| PR14 | `nswamy/pal-pr14-offsetof` | `main` |
| PR15 | `nswamy/pal-pr15-initializer-lists` | `main` |
| PR16 | `nswamy/pal-pr16-local-address-not-null` | `main` |
| PR17 | `nswamy/pal-pr17-goto-label-diagnostics` | `main` |
| PR18 | `nswamy/pal-pr18-unreachable` | `main` |
| PR19 | `nswamy/pal-pr19-switch-enum-scrutinee` | `main` |
| PR20 | `nswamy/pal-pr20-switch-default-and-if-chain` | `main` |
| PR21 | `nswamy/pal-pr21-switch-jump-abort` | PR20 + PR18 |
| PR22 | `nswamy/pal-pr22-pointer-typedef-attrs` | `main` |
| PR23 | `nswamy/pal-pr23-const-typedef` | PR22 + PR28 |
| PR24 | `nswamy/pal-pr24-const-param-modes` | PR23 |
| PR25 | `nswamy/pal-pr25-rvalue-member` | `main` |
| PR26 | `nswamy/pal-pr26-rewrites-to` | PR25 + PR28 |
| PR27 | `nswamy/pal-pr27-nullable-out` | PR05 |
| PR28 | `nswamy/pal-pr28-nullable-caller-transfer` | PR27 |
| PR29 | `nswamy/pal-pr29-nullable-decline` | PR23 (which carries PR28) |
| PR30 | `nswamy/pal-pr30-memset-wrapper` | PR10 |
| PR31 | `nswamy/pal-pr31-annotated-tail-conditional` | `main` |
| PR32 | `nswamy/pal-pr32-todo-reproducer` | `main` |
| PR33 | `nswamy/pal-pr33-inline-pulse-ensures` | PR26 + PR06 |
