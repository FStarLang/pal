# Proving C with PAL (Proof-oriented Annotation Language) + F*/Pulse

This guide captures the working knowledge needed to verify C code using PAL. This skill is written for a *consumer project* that uses PAL as a sibling clone. In the following we describe how to use PAL as a tool to verify C code.

PAL is a tool for verifying C code annotated with specifications. At a high-level, PAL converts C code and accompanying specifications to Pulse code that is then verified using the F* proof engine. Annotations on the C code direct what specifications are given to the translated code. In some cases, annotations also direct whether Pulse sees a pointer as just a simple data pointer or as an array.

## The high-level workflow
Let us look at a high-level workflow for proving with PAL.

1. **Read the C code.** Identify ownership up front: which pointers are arrays, which are consumed, which are out-params, which must stay live across a loop.
2. **Add ownership annotations before functional specs.** `_array`, `_consumes`, `_out`, `_plain` change the *generated representation*. Getting these wrong (e.g. a missing `_array`) produces the wrong slprop and a cascade of `(admit())`s downstream — fix representation first.
3. **Translate, then take an "admit census."** Run PAL and triage the generated F*:
   - `grep -rn '(admit())' <outdir>` — every hit is a construct PAL could not translate.
   - Read `TranslationErrors.fst` and `diagnostics.json` for hard frontend errors.
   - Report the errors to the user. These might stem from PAL bugs that need to be addressed at the PAL level.
   - **Ignore `assume val …__aux_raw_*` / `…__pred`** — these are the *expected* axiomatized struct/array plumbing, not failures.
4. **Verify incrementally, one file at a time.** Iterate on a single `Func_*.fst` (don't run the full build between edits), read the generated `requires`/`ensures`/body to see what Pulse must prove, and discharge obligations one at a time with `_invariant`/`_ensures`/`_requires`/helpers.

The rest of this guide is organized around the two activities you alternate between once translation succeeds: **Part A — Specifying** (annotations that tell PAL/Pulse *what* must hold) and **Part B — Progressing the proof** (helper lemmas + ghost code that help Pulse discharge what's left). *Setup* and *Reference* bracket them; the *Habits* checklist (Reference) expands the steps above.

## Setup

### Toolchain layout

- **PAL binary**: `${PAL_DIR}/target/release/pal`. The PAL repo is a sibling clone, *not* a submodule. Set `PAL_DIR` before any make/verify command. PAL parses C with annotations and emits one F* file per C function (`Func_*.fst{,i}`), per struct (`Struct_*.fst`), and per typedef (`Typedef_*.fst`) into `build/pal-core/`. Each of these files contain the Pulse translation of the relevant C code.
- **Pulse**: F*'s separation-logic DSL (`#lang-pulse`). All ownership/heap reasoning runs in Pulse; pure math is plain F*.
- **Hand-authored helpers**: put your Pulse proof lemmas/ghost fns in `src/core/proofs/Helpers_<MODULE>.fst`. The build picks them up via `PROOFS_DIR` in `scripts/verify.mk`. Prefer this over `_include_pulse(...)` blobs in the C file — easier to edit, reuse, and re-verify.

### Build / verify commands

```bash
# Regenerate F* from annotated C
PAL_DIR=/path/to/pal /path/to/pal/target/release/pal \
  -I src/inc -I src/core --outdir build/pal-core src/core/<file>.c

# Verify a single F* file (fast iteration)
PAL_DIR=/path/to/pal scripts/fstar.sh \
  --cache_checked_modules --cache_dir build/pal-core/_cache \
  --already_cached Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore \
  --include build/pal-core --include src/core/proofs \
  <path/to/single/File.fst>

# Full build (will stop at first F* error)
PAL_DIR=/path/to/pal make
```

When iterating on a helpers .fst, delete its `.checked` file plus any downstream func `.checked` files in `build/pal-core/_cache/` before re-verifying — otherwise stale caches mask your changes.

`fstar.sh` only accepts ONE file per invocation when `--ext fly_deps` is on. Verify each file with a separate call.

## Part A — Specifying: annotations

Annotations on the C source declare *what* must hold. They come in two flavours: **ownership** annotations that fix the generated memory representation (`_array`, `_consumes`, `_out`, `_plain`), and **functional** contracts that constrain values (`_requires`, `_ensures`, `_invariant`, `_refine`). Ownership comes first — a wrong representation may produce admits that no functional spec can fix.

### Annotation cheat-sheet

This is the proof-relevant subset; [`pal_surface_syntax.md`](pal_surface_syntax.md) is the complete annotation reference with exact lowering.

| Annotation | Where | Effect |
|---|---|---|
| `_requires(prop)` | function/loop | Pure precondition (Prims.prop) |
| `_ensures(prop)` | function/loop | Pure postcondition; loops default to `¬cond` if absent — see *Loops* below |
| `_invariant(prop)` | loop | Slprop or pure prop kept across iterations |
| `_requires(_inline_pulse(slprop))` | function | Custom slprop precondition |
| `_ensures(_inline_pulse(slprop))` | function | Custom slprop postcondition |
| `_ghost_stmt(call)` | C body | Inserts a Pulse ghost call into the generated body (the apply mechanism — see Part B) |
| `_plain` | param | Suppresses auto-emitted `pts_to`/typedef ownership for that param (you must add it manually) |
| `_array T*` | param/typedef field | Maps to Pulse `array T` |
| `_refine(prop)` | typedef / struct / union / field | Adds a `with_pure` clause to the type's `__pred`. Holds invariantly for every value of the type. To embed an arbitrary slprop / reference the spec parameter, use the `(_slprop) _inline_pulse(...)` escape hatch — see *Spec-design idioms* below. |
| `_refine_value(name, prop)` | all types | Same, but names the existentially-bound spec value so it can be referenced in `prop` |
| `_let(...)` / `_letimpure(...)` | top-level | Define a pure/slprop helper visible in annotations |
| `_specint` | expression cast | Lifts a C integer expression to mathematical `int` (no overflow) |
| `_live(x)` | invariant | Asserts `x` is live (typically used as a loop invariant for stack-locals) |

### Antiquotation inside `_inline_pulse(...)`

- `$(x)` — value of a parameter or local `x`. In ghost expressions on a mutable parameter, it becomes `!var_x` in body context and `var_x` in spec context.
- `` $`name `` — introduces a fresh existential of inferred type bound in the surrounding `exists*`. Use for spec values you can't otherwise name.
- `$(return)` — the function's return value (use inside `_ensures`).
- `$&(local)` — address-of a local (use for `pts_to`-style refs to stack locals).
- `$unfold-uninit(T)`, `$fold-uninit(T)` — open/close per-field uninit reps for typedef `T` (ghost-code application — see Part B). `$unfold-uninit` is *not* auto-applied — see *`[@@pulse_intro]`* in Part B.
- `$unfold(T)`, `$fold(T)` — same for initialized reps (Part B).

### Functions: spec & ensures shapes

A function `_ensures(slprop)` becomes a Pulse `ensures` clause in the generated F* signature. Multiple `_ensures` clauses are conjoined via `**`.

**Auto-emitted ensures**: PAL automatically adds `exists* val_return_0. ty_T__pred return_1 1.0R val_return_0` for a value-returning function. **`val_return_0` is bound inside that `exists*` — separate `_ensures` clauses cannot reference it.** If you need to talk about the spec from a custom `_ensures`, two options:

1. **Universally quantify** over `spec` and add an implication gated on the typedef bounds:
   ```c
   _ensures(_inline_pulse(pure (
     forall (spec) (nt).
       <typedef bounds on return + spec> ==> my_inv $(return) spec nt)))
   ```
2. Use `_refine_value(name, ...)` on the typedef so `name` is the canonical binding everywhere.

Pure ensures are wrapped as `_ensures(_inline_pulse(pure (...)))` — this adds a `(pure P)` slprop to the ensures (no ownership conflict, no duplicated typedef pred).

### Loops: invariants, ensures, and `break`

```
while (cond)
  _invariant(slprop_or_pure)   // one or more
  _ensures(pure_prop)          // pure prop (Prims.prop), NOT slprop
{ body }
```

Key facts:

- **`_invariant` accepts slprop or pure** (wrap a slprop with `_inline_pulse(...)`). Holds at top of every iteration and after each iteration.
- **`_ensures` on a loop is a `Prims.prop`, not a slprop.** Wrapping a slprop will fail **Error 12** (slprop vs prop mismatch).
- **If you omit `_ensures`, Pulse defaults the loop-exit pure obligation to `¬cond`.** Natural exit satisfies this, but `break` doesn't (you exit with `cond = true`). Result: `false == cond` VC at the break — **Error 19** with the body's `_if_hyp` in context.
- **Fix for `break`**: add an `_ensures(p)` stating a fact that actually holds at the break — it replaces the default `¬cond` as the loop's exit obligation. Write one `_ensures` per break site (each is a disjunct of the exit condition). It only needs to be *provable* at the break, so `_ensures(true)` works in a pinch, but a useful fact (e.g. `_ensures(i <= n)` in `break_continue.c`) is usually what you want so downstream code can rely on it. The slprop invariant is preserved at break automatically; only the pure exit prop needs restating. See [`pal_surface_syntax.md`](pal_surface_syntax.md) §Loop invariants and `pal/test/break_continue/break_continue.c`.

The slprop loop invariant is what survives both natural exit and `break`; no need to restate it as `_ensures`.

### Spec-design idioms

#### Factor out NewTime-independent "shape" invariants

Wrap typedef bounds + structural invariants (e.g., monotonicity) in a `struct_inv v spec` pure prop. Make per-context invariants (e.g., loop invariants involving a NewTime) layer on top:

```fst
let struct_inv v spec : prop = <typedef bounds> /\ monotone_at spec ...
let loop_inv_pure v spec nt : prop = struct_inv v spec /\ valid_new_time_at spec ... nt
```

This makes `struct_inv` reusable in other functions that touch the struct (e.g., as a carry-along bundled invariant).

#### Bake stronger invariants into `_refine` when every function can re-establish them

The typedef `_refine` clause holds **invariantly across the entire lifecycle** of every value of the typedef. Putting a strong invariant (e.g., monotonicity of a deque) there is sound *as long as every public function that takes the struct can re-establish the invariant on return*. Functions that transiently break the invariant in their body are fine — once they unfold the typedef pred they operate on raw `pts_to` / `array_pts_to_full` and only need the invariant back at the `fold`/return boundary.

Bundling `struct_inv` into `_refine` is preferable to having every caller thread `_requires`/`_ensures(_inline_pulse(pure (struct_inv ...)))` clauses — fewer per-function annotations, and Pulse picks up the invariant directly from the auto-emitted `__pred` slprop.

**The encoding.** PAL's plain `_refine(<C expr>)` syntax can only express bool conjuncts over `this.<field>` / `this.<field>._length` projections. To call a hand-authored helper (which can reference the spec parameter of the typedef pred and return a `prop`), drop into the `_inline_pulse(...)` escape hatch with a `(_slprop)` cast and call the helper from inside `pure (...)`:

```c
_refine((_slprop) _inline_pulse(
    pure (Helpers_X.struct_inv this
            val_this_0.SW.struct_..__spec__<field>_0)
))
```

The struct invariant itself becomes the single source of truth, defined in the helpers module:

```fst
let struct_inv (v: SW.struct_X) (spec: CA.full_array_spec ENTRY) : prop =
    UInt32.v v.SW.struct_..__cap == CA.array_spec_len spec /\
    ... (other bool bounds) ...
    /\ monotone_at spec ...
```

Two things that make this work:

1. **`(_slprop)` cast on `_inline_pulse(...)`** — the only F\*-flavored cast PAL's C-frontend recognises here (alongside `(_specint)`). There is no `(prop)`. The cast tells PAL to embed the verbatim F\* text as an slprop directly without an implicit `with_pure` wrap. Wrap the body in `pure (...)` so it lifts the `prop`-typed helper application to slprop position; this composes with the auto-emitted `Struct_X__pred ...` via `**`.
2. **`val_this_0` is in scope inside the inline pulse body** — it is the spec parameter of the auto-generated `ty_X__pred` predicate. PAL's `subst_this_rvalue` only substitutes `this`; everything else in the verbatim text resolves against the typedef pred's bindings. Use it to reach spec fields like `val_this_0.SW.struct_..__spec__<field>_0` so the helper can talk about the ghost view of array-typed fields.

Inlining bool conjuncts directly (without factoring through a helper):

If you don't want a separate helper, you can also inline `prop`-flavored bool conjuncts directly inside the `pure (...)` block. One extra gotcha applies in that case:

- **`<: nat` ascription on `==`** when comparing `FStar.UInt32.v X` (type `uint_t 32`) to `array_spec_len S` (type `nat`). Without it F\* picks `uint_t 32` for both sides and fails the subtype check on the rhs ("Expected `uint_t 32`, got `nat`"). Ascribing the lhs to `nat` lifts both sides to the common supertype. Inside a helper definition this isn't needed because the helper picks `prop` for `==` immediately.

Other gotchas (apply to both forms):

- The body of `_inline_pulse(...)` is verbatim F\* — you bypass PAL's `_specint` lifting, `._length` sugar (`this.X._length` → `reveal (length_of this.X)`), and `&&`-vs-`**` overload. Write the F\* form by hand: `FStar.UInt32.v`, `array_spec_len`, `/\` (not `&&`).
- F\*'s `/\` cannot appear in a plain `_refine(...)` body — PAL would tokenize it as `/` followed by stray `\`. Inside `_inline_pulse(...)` it's fine because the body bypasses PAL's C-tokenizer entirely.

**When NOT to use this.** If even one function in the API genuinely cannot re-establish the bundled invariant on return (legacy mutators, partial-update setters), keep it as a free-standing helper that contracts thread explicitly. Don't trap yourself by baking it into `_refine`.

#### Use named F\* constants — never `pow2` or numeric literals

**Always** express integer bounds via `FStar.UInt.max_int` / `FStar.Int.max_int` / `FStar.Int.min_int`, both in C-side spec annotations (`_requires`, `_refine`, `_inline_pulse`) and in F\* helper definitions. This matches C's `<stdint.h>` macros (`UINT64_MAX`, `INT32_MIN`, …), reads as the intended semantic constraint, and avoids subtle off-by-one bugs that come from mixing `<` / `<=` with `pow2 n`.

| Use this | Not this |
|---|---|
| `FStar.UInt.max_int 64` | `pow2 64 - 1`, `0xFFFFFFFFFFFFFFFF`, `18446744073709551615` |
| `x + y <= FStar.UInt.max_int 64` | `x + y < pow2 64` |
| `FStar.Int.max_int 32` for `INT32_MAX` (2^31 − 1) | `pow2 31 - 1` |
| `FStar.UInt.max_int 32` for `UINT32_MAX` (2^32 − 1) | `pow2 32 - 1` |
| `FStar.Int.min_int 32` for `INT32_MIN` | `- pow2 31` |

In C-side annotations, use `INT32_MAX` / `UINT32_MAX` / `INT32_MIN` from `<stdint.h>` for runtime values, and the F\*-side `max_int` form inside `_inline_pulse(pure (...))` blocks.

Example (`QUIC_SUBRANGE` invariant, inlined in `range.h`):

```c
_refine((_slprop) _inline_pulse(
    pure (FStar.UInt64.v this.Struct_QUIC_SUBRANGE.struct_quic_subrange__count >= 1
       /\ FStar.UInt64.v this.Struct_QUIC_SUBRANGE.struct_quic_subrange__low
          + FStar.UInt64.v this.Struct_QUIC_SUBRANGE.struct_quic_subrange__count
          <= FStar.UInt.max_int 64)
))
```

#### Inline vs. helper-file for typedef invariants

- **Inline `_refine((_slprop) _inline_pulse(pure (...)))`** when the invariant is a few short pure conjuncts. Keeps the C header self-contained.
- **Separate `Helpers_<TYPE>.fst`** when the invariant is multi-line, branches on a field (e.g. inline-vs-heap case split), references a spec parameter, or is referenced from helper lemmas. See `Helpers_QUIC_RANGE.fst` for the case-split pattern, `Helpers_QUIC_SLIDING_WINDOW_EXTREMUM.fst` for the spec-parameter pattern.

## Part B — Progressing the proof: helper lemmas + ghost code

When the representation and specs are right but Pulse still can't close a goal automatically, you progress the proof operationally: **define a helper lemma or ghost fn** in `Helpers_<MODULE>.fst`, then **apply it at the failing program point** with `_ghost_stmt(...)`. The patterns below are the recurring ones — most boil down to "make a fact or a points-to syntactically present so Pulse's matcher can find it."

### Pulse mechanics you must know

#### `[@@pulse_unfold]` / `[@@pulse_eager_unfold]`

Attach to slprop definitions you want Pulse to silently unfold at use sites. Without one of these, loop-condition reads (e.g., `Window->WindowSize > 0`) fail with **Error 228** because the opaque slprop hides the `pts_to`. `pulse_eager_unfold` is more aggressive; either works for loop invariants.

#### `[@@pulse_intro]` — lemmas Pulse applies automatically

PAL tags the generated fold/unfold lemmas with `[@@pulse_intro]`. Pulse's prover applies a `[@@pulse_intro]` lemma *on its own* whenever it needs to prove an slprop that appears in that lemma's postcondition — you never write a `_ghost_stmt` for it. For a struct `foo` the auto-applied lemmas are:

| Lemma | Pulse applies it when it needs… |
|---|---|
| `struct_foo__aux_raw_unfold` | a per-field `pts_to` / `array_pts_to` (unfolds the struct) |
| `struct_foo__aux_raw_fold` | the whole-struct `pts_to x (Mkfoo …)` |
| `struct_foo__aux_raw_fold_uninit` | `pts_to_uninit x` back from the per-field uninit reps |
| `struct_foo__pred_unfold` / `struct_foo__pred_fold` | to (de)compose `struct_foo__pred` into the field `pts_to`s |
| `union_foo__<fld>__aux_raw_unfold` / `__aux_raw_fold` | the union per-field analogues |

So **when you unfold a struct, `aux_raw_unfold` is applied for you**: a field read like `s->p` exposes that field's `pts_to`/`array_pts_to` with no ghost call.

**The lone exception is `struct_foo__aux_raw_unfold_uninit`**, which PAL emits *without* `[@@pulse_intro]`. Pulse will not apply it on its own, so to open a fresh, not-yet-initialized struct (e.g. a stack-local before its fields are written) you must apply it manually:

```c
_ghost_stmt($unfold-uninit(foo) $&(local));   // lowers to struct_foo__aux_raw_unfold_uninit
```

You can also put `[@@pulse_intro]` on your *own* helper lemmas (Part B) to have Pulse apply them automatically instead of inserting a `_ghost_stmt` call at every use site.

#### Implicit-arg inference via the slprop matcher

Pulse picks witnesses for `#`-implicit args by matching slprop *names* in the current context against the function's preconditions. **Two pitfalls**:

1. **Field-projected slprops drag the wrong existential.** If your loop invariant says `array_pts_to_full v.extremums spec` and the body mutates `v` (via a `pts_to w v` write), Pulse picks `v := old_v` from the array slprop after the write and refuses the `pts_to w new_v`/`v.extremums` mismatch. **Fix: hoist the array reference as a separate existential.** Add `e : array T` and `pure (v.extremums == e)`, then `array_pts_to_full e spec` is keyed on a stable name across writes.
2. **`length_of` cannot appear inside `pure (...)`.** It's a Pulse ghost fn. Use `CA.array_spec_len spec` (a pure `GTot`) instead.

#### Fold/unfold pattern for opaque loop invariants

```fst
[@@pulse_unfold]
let loop_inv (w: ref ...) (...) : slprop =
  exists* v e spec.
    pts_to w v ** array_pts_to_full e spec **
    pure (v.extremums == e /\ inv_pure v spec ...)

ghost fn loop_inv_unfold w ... requires loop_inv w ... ensures (exists* v e spec. ...) { unfold (loop_inv w ...) }

ghost fn loop_inv_fold (#v) (#e) (#spec) w ...
  requires (pts_to w v ** array_pts_to_full e spec ** pure (v.extremums == e /\ inv_pure v spec ...))
  ensures loop_inv w ...
{ fold (loop_inv w ...) }
```

In the C body, call them via `_ghost_stmt`:
```c
_ghost_stmt(Helpers_X.loop_inv_unfold $(Window));
// ... body manipulates pts_to, array_pts_to_full, pure facts ...
_ghost_stmt(Helpers_X.loop_inv_fold $(Window));
```

#### Bridges for slprop "shape" mismatches

When the loop invariant carries `array_pts_to_full e spec` but the body needs `array_pts_to_full v.extremums spec` (or vice versa), write a ghost that does a single `rewrite` using the pure equality:

```fst
ghost fn bridge_e_to_v (#v) (#e) (#spec) (w: ref ...)
  requires pts_to w v ** array_pts_to_full e spec ** pure (v.extremums == e)
  ensures  pts_to w v ** array_pts_to_full v.extremums spec ** pure (v.extremums == e)
{ rewrite (array_pts_to_full e spec) as (array_pts_to_full v.extremums spec) }
```

Avoid trying to bridge the other direction from the C body if it requires Pulse to *invent* the hoisted existential — you'll get **Error 339** ("can't infer implicit argument"). Instead, fold the full loop invariant directly; its precondition gives Pulse the names it needs.

#### Pulse ghost-fn body syntax

- `let x = e;` (statement form, semicolon, **not** `let x = e in`).
- `fold (P args)` (must include args, not bare name).
- `unfold (P args)`.
- `rewrite slprop1 as slprop2` for spatial rewrites using a `pure` equality already in scope.
- `with x. P` and `assume_ ...` etc. for advanced patterns.

### Initialization & in-place mutation patterns

```c
QUIC_X Window;
_ghost_stmt($unfold-uninit(QUIC_X) $&(Window));  // open per-field uninit reps
CXPLAT_DBG_ASSERT(...);                          // optional preconditions
Window.Field1 = v1;                              // per-field writes
Window.Field2 = v2;
...
_ghost_stmt($fold(QUIC_X) $&(Window) _ _ _ _ _); // re-fold to pts_to w (Mkstruct ...)
return Window;
```

For pointer params, use `$unfold(QUIC_X) $(Window)` / `$fold(QUIC_X) $(Window) _ ...` instead.

When a statement has a non-unit return type (e.g., `Window->WindowSize--` returns `UInt32.t`), the F* statement must discharge that value. PAL emits `(Pulse.Lib.C.UnaryOps.minusminuspost_uint32 var_x)` — fine when followed by more statements; fails with **Error 76** if it's the trailing statement of a block. Fix: append `_ghost_stmt(())` after it.

### Habits

1. **Read PAL test examples first** when you hit a new annotation: `pal/test/break_continue` for break/continue loops, `pal/test/compound_ops` for `++`/`--` postfix, `pal/test/arrayptrs` for arrayptr handling, `pal/test/dpe` for richer typedef refinements with `_refine_value`.
2. **Iterate on a single F* file** (`scripts/fstar.sh path/to/Func_X.fst`) rather than running full `make` between every change.
3. **Open the generated `.fst` after every PAL change**. Read the generated `requires`/`ensures`/body to see what Pulse actually has to prove. The C-side annotation can be unambiguous to read but generate surprising F*.
4. **Don't blindly bump rlimits** when a proof times out. Diagnose the matcher/inference issue first; nearly every "long proof" we hit had a structural fix (hoist an existential, change opaqueness, restructure the invariant) that made it cheap.
5. **Don't modify C function bodies** unless explicitly authorized. Add annotations, `_ghost_stmt` calls, and `_invariant`/`_ensures`/`_requires` clauses only. Comment out problematic bodies but never delete.
6. **Helpers stay in `src/core/proofs/Helpers_*.fst`**, not inline in C. Keep their `let` definitions small and well-named (`struct_inv`, `expire_loop_inv_pure`, etc.) — the names appear in goals and error messages.
7. **Use `_ghost_stmt`** to inject ghost calls in the body when Pulse needs facts in the SMT context (e.g., `valid_new_time_at_head_g` to derive `NewTime ≥ Head.Time` before a subtraction VC).
8. **Get an independent critique** (rubber-duck) before non-trivial structural changes to invariants — Pulse matcher behavior is subtle, and a bad invariant shape can cost hours.

### Where to look for examples

- `pal/test/<topic>/<topic>.c` for the canonical PAL annotation patterns; generated F* lives in `pal/test/<topic>/out/`.
- `pal/pulse/` for the supported Pulse syntax (`syntax.md`).
- `~/.local/fstar/lib/fstar/pulse/pulse/syntax.md` for the bundled Pulse syntax reference.
- F* stdlib (`~/.local/fstar/lib/fstar/ulib/`) for `FStar.Int.*`, `FStar.UInt.*`, `FStar.Seq.*`, `FStar.Classical.*`.
