# Proving C with PAL (Proof-oriented Annotation Language) + F*/Pulse

A high-level guide for adding and verifying proof annotations on C code using
PAL → F*/Pulse. It covers **compiling/verifying**, **writing specs** (ownership
first, then functional contracts), and the **proving idioms** that recur once
you move past trivial functions.

All examples below use a neutral running type — a dynamic-array "container":

```c
typedef struct CONTAINER {
    _array ELEM* Elems;     // points into Inline OR a heap allocation
    uint32_t     Count;     // number of live elements (used length)
    uint32_t     Capacity;  // allocated length
    ELEM         Inline[N]; // inline small-vector storage
} CONTAINER;
```

Substitute your own struct, fields, and helper-module names throughout. The
conventions (`Helpers_X.fst`, `obj_inv`, `loop_inv`, `struct_inv`, …) are just
naming suggestions.

---

## 1. Toolchain layout

- **PAL binary**: `${PAL_DIR}/target/release/pal`. The PAL repo is typically a
  sibling clone, *not* a submodule. Set `PAL_DIR` before any make/verify command.
- **Translator role**: PAL parses annotated C and emits one F* file per C
  function (`Func_*.fst{,i}`), per struct (`Struct_*.fst`), and per typedef
  (`Typedef_*.fst`) into a generated output directory (e.g. `build/pal-core/`).
- **Pulse**: F*'s separation-logic DSL (`#lang-pulse`). All ownership/heap
  reasoning runs in Pulse; pure math is plain F*.
- **Hand-authored helpers**: put your Pulse proof lemmas/ghost fns in a
  `Helpers_<MODULE>.fst` next to the generated output (e.g. under
  `src/core/proofs/`). The build picks them up via a proofs include dir. Prefer
  this over `_inline_pulse(...)` blobs in the C file — easier to edit, reuse,
  and re-verify. Helper names appear in goals and error messages, so keep them
  small and descriptive (`struct_inv`, `loop_inv`, `foo_fold`).

## 2. Build / verify commands

```bash
# Regenerate F* from annotated C
PAL_DIR=/path/to/pal /path/to/pal/target/release/pal \
  -I <public-include-dir> -I <internal-include-dir> \
  --outdir build/pal-core src/.../<file>.c

# Verify a single F* file (fast iteration loop)
PAL_DIR=/path/to/pal scripts/fstar.sh \
  --cache_checked_modules --cache_dir build/pal-core/_cache \
  --already_cached Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore \
  --include build/pal-core --include <proofs-dir> \
  build/pal-core/Func_<Name>.fst

# Verify one file through the dependency-aware Makefile (same cache as full build)
PAL_DIR=/path/to/pal make -f scripts/verify.mk \
  build/pal-core/_cache/Func_<Name>.fst.checked

# Full translate + verify
PAL_DIR=/path/to/pal make            # or: make -j$(nproc) verify; stops at first error
PAL_DIR=/path/to/pal make translate  # translation only

# Full translate and verify beyond the first error
PAL_DIR=/path/to/pal make -k


```

**Fast iteration loop.** Edit the C file or a `Helpers_*.fst`, run
`make translate` (PAL re-runs only if a tracked C file changed — `touch` the C
file to force), then delete the specific `.checked` file under
`build/pal-core/_cache/` and re-run the single-file verify. This is far faster
than a full `make verify`: F*'s dep graph only re-checks the requested module
and any dependency whose `.checked` is missing.

**Cache invalidation.** When iterating on a helper `.fst`, delete its `.checked`
file **plus** any downstream func `.checked` files in `build/pal-core/_cache/` —
otherwise stale caches mask your changes.

**Single-file limit.** Some F* runner wrappers accept only ONE file per
invocation when `--ext fly_deps` is on. Verify each file with a separate call.

## 3. C annotation cheat-sheet

Two flavours of annotation: **ownership** annotations fix the generated memory
representation; **functional** contracts constrain values. Get ownership right
*first* — a wrong slprop cascades into admits no functional spec can repair.

| Annotation | Where | Effect |
|---|---|---|
| `_requires(prop)` | function/loop | Pure precondition (`Prims.prop`) |
| `_ensures(prop)` | function/loop | Pure postcondition; loops default to `¬cond` if absent — see §6 |
| `_requires(_inline_pulse(slprop))` | function | Custom slprop precondition |
| `_ensures(_inline_pulse(slprop))` | function | Custom slprop postcondition |
| `_invariant(prop)` | loop | Slprop or pure prop kept across iterations |
| `_ghost_stmt(call)` | C body | Inserts a Pulse ghost call into the generated body |
| `_plain` | param/typedef | Suppresses auto-emitted `pts_to`/typedef ownership (you add it manually) |
| `_array T*` | param/typedef field | Maps to Pulse `array T` (initialized ownership: `array_pts_to_full`) |
| `_arrayptr T*` | param | Maps to a Pulse *arrayptr*: a zero-length pointer into a parent array that borrows the parent's permission — see §10.11 |
| `_consumes` | param | The function *takes* the param's `pts_to`/array ownership and does not return it (it is freed or moved out) — no ownership in the post |
| `_out` | param | Out-parameter: caller passes uninitialized storage (a `pts_to_uninit` precondition); callee writes it, post is initialized |
| `_preserves(_inline_pulse(slprop))` | function | Borrow a slprop across the call: appears unchanged in *both* requires and ensures (sugar for `requires P ** … ensures P ** …`) |
| `_refine(prop)` | typedef/struct/field | Adds a `with_pure` clause to the type's `__pred`; holds invariantly. Use the `(_slprop) _inline_pulse(...)` escape hatch to embed an arbitrary slprop or reference the spec parameter — see §9. |
| `_refine_value(name, prop)` | type | Same, but names the existentially-bound spec value so `prop` can reference it |
| `_let(...)` / `_letimpure(...)` | top-level | Define a pure/slprop helper visible in annotations |
| `_specint` | expression cast | Lifts a C integer expression to mathematical `int` (no overflow) |
| `_live(x)` | invariant | Asserts `x` is live (typically a loop invariant for stack-locals) |

### Antiquotation inside `_inline_pulse(...)`

- `$(x)` — value of a parameter or local `x`. For a mutable parameter it becomes
  `!var_x` in body context and `var_x` in spec context.
- `` $`name `` — introduces a fresh existential of inferred type bound in the
  surrounding `exists*`. Use for spec values you can't otherwise name.
- `$(return)` — the function's return value (use inside `_ensures`).
- `$&(local)` — address-of a local (for `pts_to`-style refs to stack locals).
- `$unfold-uninit(T)` / `$fold-uninit(T)` — open/close per-field *uninit* reps
  for typedef `T`. `$unfold-uninit` is **not** auto-applied.
- `$unfold(T)` / `$fold(T)` — same for *initialized* reps.

## 4. Pulse mechanics you must know

### The permission model: who can read, who can write

Every `pts_to` / `array_pts_to` carries a **permission** `p : perm`, a value in
`(0.0R, 1.0R]` (the `R` suffix denotes a `perm`/real literal).

- **`1.0R` is full permission** — required to *write* (or free). `pts_to r v`
  defaults to `1.0R`; `pts_to r #p v` / `array_pts_to a p s` state it explicitly.
- **A fractional permission `#p` (e.g. `0.5R`) is read-only.** Reads and ghost
  observations need *any* `p > 0.0R`; you cannot mutate below full.
- **Split and recombine.** `share` turns `pts_to r #p v` into two halves
  `pts_to r #(p /. 2.0R) v ** pts_to r #(p /. 2.0R) v` (two readers); `gather`
  fuses them back to recover write permission. Pass `#p` to give a callee read
  access without surrendering ownership.
- **`_preserves` / `preserves P`** is the borrow idiom: hold `P` across a call at
  whatever permission you have and get it back unchanged.

Rule of thumb: **the smallest permission that type-checks is the most reusable.**
Spec readers and fact-surfacing ghosts take `#p`; mutators take `1.0R`. A "cannot
prove `pts_to r 1.0R v`" error where the context only has `pts_to r #p v` means
you tried to write through a borrowed (fractional) reference.

### `[@@pulse_unfold]` / `[@@pulse_eager_unfold]`

Attach to slprop definitions you want Pulse to silently unfold at use sites.
Without one of these, loop-condition reads (e.g., `obj->Count > 0`) fail with
**Error 228** because the opaque slprop hides the `pts_to`. `pulse_eager_unfold`
is more aggressive; either works for loop invariants.

### Implicit-arg inference via the slprop matcher

Pulse picks witnesses for `#`-implicit args by matching slprop *names* in the
current context against the function's preconditions. **Two pitfalls:**

1. **Field-projected slprops drag the wrong existential.** If your loop
   invariant says `array_pts_to_full v.elems spec` and the body mutates `v` (via
   a `pts_to r v` write), Pulse picks `v := old_v` from the array slprop after
   the write and refuses the `pts_to r new_v` / `v.elems` mismatch.
   **Fix: hoist the array reference as a separate existential.** Add
   `e : array T` and `pure (v.elems == e)`, then `array_pts_to_full e spec` is
   keyed on a stable name across writes.
2. **`length_of` cannot appear inside `pure (...)`.** It is a Pulse ghost fn.
   Use `array_spec_len spec` (a pure `GTot`) instead.

### Fold/unfold pattern for opaque loop invariants

```fst
[@@pulse_unfold]
let loop_inv (r: ref ...) (...) : slprop =
  exists* v e spec.
    pts_to r v ** array_pts_to_full e spec **
    pure (v.elems == e /\ inv_pure v spec ...)

ghost fn loop_inv_unfold r ... requires loop_inv r ... ensures (exists* v e spec. ...)
{ unfold (loop_inv r ...) }

ghost fn loop_inv_fold (#v) (#e) (#spec) r ...
  requires (pts_to r v ** array_pts_to_full e spec ** pure (v.elems == e /\ inv_pure v spec ...))
  ensures loop_inv r ...
{ fold (loop_inv r ...) }
```

In the C body, call them via `_ghost_stmt`:

```c
_ghost_stmt(Helpers_X.loop_inv_unfold $(Obj));
// ... body manipulates pts_to, array_pts_to_full, pure facts ...
_ghost_stmt(Helpers_X.loop_inv_fold $(Obj));
```

### Bridges for slprop "shape" mismatches

When the invariant carries `array_pts_to_full e spec` but the body needs
`array_pts_to_full v.elems spec` (or vice versa), write a ghost that does a
single `rewrite` using the pure equality:

```fst
ghost fn bridge_e_to_v (#v) (#e) (#spec) (r: ref ...)
  requires pts_to r v ** array_pts_to_full e spec ** pure (v.elems == e)
  ensures  pts_to r v ** array_pts_to_full v.elems spec ** pure (v.elems == e)
{ rewrite (array_pts_to_full e spec) as (array_pts_to_full v.elems spec) }
```

Avoid bridging the direction that requires Pulse to *invent* the hoisted
existential — you'll get **Error 339** ("can't infer implicit argument").
Instead fold the full loop invariant directly; its precondition gives Pulse the
names it needs.

### Pulse ghost-fn body syntax

- `let x = e;` (statement form, semicolon, **not** `let x = e in`).
- `fold (P args)` / `unfold (P args)` — must include args, not a bare name.
- `rewrite slprop1 as slprop2` — spatial rewrite using a `pure` equality already
  in scope.
- `with x. P` and `introduce exists* ... with ...` for explicit existentials
  (see §13).

### Reading the generated F*: file layout and naming

After `make translate`, each C entity becomes one F* module. **Read them** — the C
annotation is concise, but the generated F* is what Pulse actually checks.

| Generated file | Contains |
|---|---|
| `Func_X.fst` / `.fsti` | the function body (`.fst`) and its spec/contract (`.fsti`). Callers see only the `.fsti`. |
| `Struct_X.fst` | the record type for `struct X` plus its `__aux_raw_*` and `__pred` fold/unfold lemmas |
| `Typedef_X.fst` | a typedef's predicate `ty_X__pred` and its reps |

Naming conventions you will meet constantly:

- **`var_X`** — PAL's mutable *cell* for C param/local `X` (from
  `let mut var_X = var_X;`). `(!var_X)` reads it; the bare signature param is also
  `var_X` (the shadow gotcha, §6.5).
- **`val_X_0`, `val_X_1`** — erased *spec* (ghost) views of a value/typedef,
  existentially bound in the auto-emitted predicate.
- **`ty_X__pred ptr p val`** — the predicate owning a typedef-`X` value at
  permission `p` with spec view `val`; `val` is in scope inside a `_refine`.
- **`Struct_X__aux_raw_unfolded` / `…__pred`** — per-field and whole-value
  ownership predicates for a struct.
- **`func_X`** — the generated Pulse `fn` for C function `X`.

Triage right after translating: `grep -rn '(admit())' build/...` — every hit is a
construct PAL could not translate. **Ignore** expected axiomatized plumbing
(`assume val …__aux_raw_*`, `…__pred`); those are not failures.

### `[@@pulse_intro]`: which fold/unfold lemmas Pulse applies for you

PAL tags most generated struct fold/unfold lemmas with `[@@pulse_intro]`, so Pulse
applies them **automatically** when it needs the corresponding shape:

| Lemma | Auto-applied when Pulse needs… |
|---|---|
| `Struct_X__aux_raw_unfold` | per-field `pts_to` / `array_pts_to` of a struct value |
| `Struct_X__aux_raw_fold` | a whole-struct `pts_to x (MkX …)` |
| `Struct_X__aux_raw_fold_uninit` | a `pts_to_uninit x` from per-field uninit reps |
| `Struct_X__pred_unfold` / `__pred_fold` | to (de)compose `Struct_X__pred` |

**The one exception**: `Struct_X__aux_raw_unfold_uninit` is emitted **without**
`[@@pulse_intro]`. To open a *fresh, uninitialized* struct you must apply it by
hand — that is exactly what `$unfold-uninit(X) $&(local)` does (§7). Forgetting
this is a common "why won't my per-field writes type-check" stall.

You can add `[@@pulse_intro]` to your *own* helper lemmas to have Pulse apply them
automatically — handy for a recurring bridge, but use sparingly: too many
auto-intro lemmas slow the matcher and can fire in unintended contexts.

## 5. Functions: spec & ensures shapes

A function `_ensures(slprop)` becomes a Pulse `ensures` clause in the generated
signature. Multiple `_ensures` clauses are conjoined via `**`.

**Auto-emitted ensures.** PAL automatically adds
`exists* val_return_0. ty_T__pred return_1 1.0R val_return_0` for a
value-returning function. **`val_return_0` is bound inside that `exists*` —
separate `_ensures` clauses cannot reference it.** To talk about the return spec
from a custom `_ensures`, either:

1. **Universally quantify** over the spec and gate on the typedef bounds:
   ```c
   _ensures(_inline_pulse(pure (
     forall (spec). <typedef bounds on return + spec> ==> my_inv $(return) spec)))
   ```
2. Use `_refine_value(name, ...)` on the typedef so `name` is the canonical
   binding everywhere.

Pure ensures are wrapped as `_ensures(_inline_pulse(pure (...)))` — adds a
`(pure P)` slprop (no ownership conflict, no duplicated typedef pred).

## 6. Loops: invariants, ensures, and `break`

```
while (cond)
  _invariant(slprop_or_pure)   // one or more
  _ensures(pure_prop)          // pure prop (Prims.prop), NOT slprop
{ body }
```

Key facts:

- **`_invariant` accepts slprop or pure** (wrap a slprop with `_inline_pulse`).
  Holds at top of every iteration and after each iteration.
- **`_ensures` on a loop is a `Prims.prop`, not a slprop.** Wrapping a slprop
  fails **Error 12**.
- **Omitting `_ensures` defaults the loop-exit pure obligation to `¬cond`.**
  Natural exit satisfies this, but `break` doesn't (you exit with `cond = true`)
  → `false == cond` VC at the break — **Error 19** with the body's `_if_hyp` in
  context.
- **Fix for `break`**: add an `_ensures(p)` stating a fact that holds at the
  break (`_ensures(true)` works; a useful fact is better). The slprop invariant
  is preserved at break automatically; only the pure exit prop needs restating.

The slprop loop invariant survives both natural exit and `break`; no need to
restate it as `_ensures`.

### A non-tail `if` that contains a `break`

Inside a loop, a non-tail `if` whose body `break`s needs its `_ensures` to
describe the **fall-through (else) continuation, not the break path**. The `break`
jumps to loop exit and must re-establish the *loop invariant* at the `break;`
itself — fold the invariant (plus any `loop_inv_fold` ghost) right before the
`break`. So the if-`_ensures` states the shape the *next in-loop statement* needs,
typically the **open** (`[@@pulse_unfold]`) twin of the invariant when the
following code still reads through the struct. The pts_to re-listing and
free-existential rules of §6.5 apply unchanged.

### Back-edge bound: fold a non-strict-counter invariant *after* the increment

If the loop invariant bundles the spec existentially and carries only a
**non-strict** counter bound (e.g. it keeps `i <= len`), re-establish it *after*
the `i++`, not before:

```c
_ghost_stmt(fold Helpers_X.inner_inv $(Obj));
i++;
_ghost_stmt(Helpers_X.loop_inv_fold $(Obj) $(i));   // AFTER i++
```

Folding the invariant *before* `i++` discards the strict `i < len` fact (carried
by the surrounding if-`_ensures`) that you need to re-prove `i + 1 <= len` at the
back-edge. Fold with the post-increment `i` while the open spec is still explicit,
and the non-strict bound discharges directly.

## 6.5. Non-tail `if`: always add `_ensures`

When a C `if` (with or without `else`) is **not the last statement of its
enclosing function body**, Pulse infers the if's post-state by joining the two
branches and unifying them. The unifier wraps shared `pure` slprops as
`match cond with | true -> p | false -> p` **even when both branches end in the
identical state**. The wrap survives across opaque slprop boundaries
(`[@@"opaque_to_smt"]` definitions like the case-split helpers in §10.2) and
walls off every downstream helper call whose precondition expects a clean
`pure p` — Error 228 fires at the next call site with the printed wrap visible
in the "In the context" dump.

**Fix**: ascribe the if's post-state with `_ensures(_inline_pulse(...))`
(requires a recent PAL with the if-`_ensures` feature). Pulse then checks each
branch directly against the ensures, skipping the inferred join.

```c
if (cond)
    _ensures(_inline_pulse(<post-state slprop>))
{
    ...
}
```

Gotchas in the ensures body:

1. **`$(X)` expands to `(!var_X)` (an stt action) in body context**, which
   slprop position rejects with Error 12. **Refer to PAL's internal local names
   directly**: `var_X` (the ref bound by PAL's `let mut var_X = var_X;` shadow),
   ghost args (not shadowed), etc. The `_inline_pulse(...)` body is parsed with
   the local scope in effect, so unqualified names resolve correctly.

2. **Every local ref's `pts_to` must be re-introduced** via existential
   bindings, even for refs the branch doesn't touch — Pulse does **not**
   auto-frame across an if-ensures. Bind values with fresh names and carry any
   safety facts the downstream code needs in pure form:

   ```c
   _ensures(_inline_pulse(
       exists* val_mid obj_v idx cnt.
           Pulse.Lib.Reference.pts_to var_obj   obj_v **
           Pulse.Lib.Reference.pts_to var_index idx **
           Pulse.Lib.Reference.pts_to var_count cnt **
           Helpers_X.obj_inv obj_v 1.0R val_mid **
           pure (UInt32.v idx + UInt32.v cnt <= UInt32.v val_mid.count
              /\ val_mid.count == var_val_pre.count)))
   ```

3. **`DBG_ASSERT(...)`-style macros are themselves non-tail ifs.** PAL lifts each
   into `if (assert_enabled()) { assert (with_pure ...) } else {}` — both
   branches are slprop no-ops, but the if-join still wraps, and consecutive
   asserts produce compounding nested wraps. Cleanest fix: **delete the assert
   from the proof source** — `_requires` already enforces the property
   statically, and the assert is a runtime no-op under `NDEBUG`.

4. **Bind the post-state via a free top-level existential, *not* via a
   record-update expression.** Write
   `exists* val_post. ... obj_inv obj_v 1.0R val_post ** pure (val_post.X == var_val_pre.X /\ ...)`
   with one pure equation per unchanged field. **Avoid**
   `exists* elems_0_post. obj_inv obj_v 1.0R ({ var_val_pre with elems_0 = elems_0_post })`
   — the nested record-update makes Pulse pre-introduce a synthetic spec name
   (e.g. `_rs_post206 := {var_val_pre with elems_0 = elems_0_post}`) into the
   body's symbolic state. Subsequent ghost-helper calls whose implicit `val_pre`
   is unified by the matcher (not by Z3 pure equalities) then fail with Error 228
   "cannot prove `case_split (UInt32.v var_val_pre.capacity <= N) ...`" because
   the in-context slprop reads `_rs_post206.capacity` and the matcher is
   syntactic. The free-existential form sidesteps this entirely.

**Tail-position ifs are exempt.** When an if is the last statement of a function
body, Pulse checks each branch against the function's own `_ensures` directly —
no synthesised join, no wrap. Place assertion-style ifs at the tail when feasible.

**Unannotated `let mut x : T;` for uninitialised C locals.** PAL emits
`let mut var_X : T;` (no initialiser) for declarations like `_array ELEM* New;`,
and Error 228 ("Allocating a mutable local variable expects an annotated
post-condition") fires at the binder. The same `_ensures(_inline_pulse(...))` on
the enclosing `if` lets the post-condition propagate to the binder. Wrap any
scope containing an uninitialised `let mut` in an if-ensures (or move the
declaration into an initialised form if the code permits).

### 6.5.1 Let-mut param-shadow drift (Error 228 at function return)

PAL emits `let mut var_X = var_X;` at the top of every function body for every C
param, rebinding the param name to a fresh cell. The function's **outer post**
is in signature scope and references the **param** (e.g. `obj_inv var_obj 1.0R
val_post`). The body's slprops reference the **cell**'s current value (via
`(!var_X)`).

When an if-`_ensures` existentializes the cell value (e.g.
`exists* obj_v. pts_to var_obj obj_v ** obj_inv obj_v 1.0R val_post`), Pulse
opens a fresh ghost name `_obj_v32` and **loses the cell = param equation**. At
function return, the matcher then fails:

```
* Error 228: Cannot prove obj_inv var_obj 1.0R val_post
  In the context:
    obj_inv _obj_v32 1.0R val_post  (* the existential's witness *)
```

Even though Z3 knows `_obj_v32 == var_obj` from `pts_to var_obj _obj_v32`, the
matcher is syntactic and can't bridge.

**Workaround.** For params the body **never reassigns** (verify with
`grep "var_X := " body.fst`), the let-mut shadow is unnecessary. Post-process the
PAL output to strip it:

```sh
# After the PAL invocation in your translate script:
sed -i \
  -e 's/  let mut var_obj = var_obj;$//' \
  -e 's/(!var_obj)/var_obj/g' \
  build/pal-core/Func_<Name>.fst
```

After the strip, the body uses `var_X` directly (the param), so the if-`_ensures`
no longer needs `pts_to var_X` clauses — keep only the slprop and pure equalities:

```c
// BAD (post-sed): refers to var_obj as a cell
exists* val_post obj_v. pts_to var_obj obj_v ** obj_inv obj_v 1.0R val_post ** pure (...)
// GOOD (post-sed): var_obj is the param directly
exists* val_post. obj_inv var_obj 1.0R val_post ** pure (...)
```

**Symptom to recognise**: Error 228 at the return-TRUE/FALSE site where the
printed *required* slprop uses the param name and the *context* slprop uses a
`_X32`-style synthetic name. This is an upstream PAL limitation; the proper fix
is for PAL to skip the let-mut shadow when the param has no body write.

### 6.5.2 Outer if-`_ensures` is mandatory when both branches return

When **both** branches of an if `return` (so the if has no fall-through join),
Pulse still synthesises a match-shaped post and tries to unify it with the
function's outer ensures:

```
* Error 228: Cannot prove
    match cond with | true -> <TRUE-arm post> | false -> <FALSE-arm post>
```

The error fires at the if's location even though every path returns. **Fix**: add
an explicit `_ensures(_inline_pulse(...))` to the outer if. Each `return` branch
discharges its own function-level post directly, and the outer `_ensures` only
needs to describe the non-returning fall-through state (or, if both branches
return, any consistent state — e.g. the preserved pre-state).

```c
if (cond_for_outer_dispatch)
    _ensures(_inline_pulse(
        exists* val_mid. obj_inv var_obj 1.0R val_mid
                      ** pure (val_mid.count == ... /\ val_mid.capacity == ...)))
{
    if (inner) { ... return TRUE; }
    else        { ... return TRUE; }
}
// outer-if FALSE arm continues here
return FALSE;
```

## 7. Initialization & in-place mutation patterns

```c
CONTAINER Obj;
_ghost_stmt($unfold-uninit(CONTAINER) $&(Obj));  // open per-field uninit reps
Obj.Field1 = v1;                                 // per-field writes
Obj.Field2 = v2;
...
_ghost_stmt($fold(CONTAINER) $&(Obj) _ _ _ _ _); // re-fold to pts_to r (Mkstruct ...)
return Obj;
```

For pointer params, use `$unfold(CONTAINER) $(Obj)` / `$fold(CONTAINER) $(Obj) _ ...`.

When a statement has a non-unit return type (e.g., `Obj->Count--` returns
`UInt32.t`), the F* statement must discharge that value. PAL emits a value-typed
action — fine when followed by more statements; fails with **Error 76** if it is
the trailing statement of a block. Fix: append `_ghost_stmt(())` after it.

### 7.1 Array-element writes: whole-element vs single-field

`Pulse.Lib.C.Array` exposes **two** kinds of element write, and PAL picks between
them based on the C statement shape:

| C statement | PAL lowering | Library fn | Precondition at slot |
|---|---|---|---|
| `arr[i] = whole_value;` (assign the *entire* element) | element-replace | `array_write` / `arrayptr_write` | `array_spec_mask` only (allocated/in-bounds) |
| `arr[i].field = v;` or `p->field = v;` (assign *one field*) | read-modify-write | `array_update` / `arrayptr_update` | `array_spec_mask` **and** `array_spec_initd` |

The single-field case lowers to
`arrayptr_update a i (fun __v __y -> { __v with ..._field = __y }) v`. The record
update `{ __v with field = __y }` **reads the current element** `__v` (via
`array_spec_idx`, only defined where `array_spec_initd`) so it can preserve the
*sibling* fields — hence the `array_spec_initd` requirement a whole-element write
does not have (`arrayptr_write` requires `array_spec_mask`; `arrayptr_update`
requires `array_spec_initd /\ array_spec_mask`).

**Known limitation — field-wise initialization of an *uninitialized* struct
array element.** PAL has **no lowering** for this. An uninit slot has
`array_spec_mask` (it is allocated — e.g. from `array_pts_to_uninit`, which
carries `array_spec_full_mask`) but **not** `array_spec_initd`. The first
`slot.field = v;` therefore lowers to `arrayptr_update`, whose `array_spec_initd`
precondition is unprovable. This is the array-element analog of the §7
stack-struct `$unfold-uninit(T)` fill — but **there is no array-element
equivalent** of `$unfold-uninit` / per-field uninit `pts_to`. It blocks any
"carve a fresh slot, then fill it field by field" pattern, e.g.:

```c
ELEM *slot = reserve_slot(Obj, i);  // returns a fresh, uninitialized slot
slot->Low   = lo;                   // FIRST field write: array_spec_initd unprovable
slot->Count = cnt;                  // (would be fine once the slot is initd)
```

This is *correct contract design*, not a missing fact: a "reserve" routine
should promise *allocated, valid-except-this-slot*, and must **not** promise the
slot's contents (the slot might only be physically zero by allocator accident —
e.g. `calloc` vs `malloc`; exposing that would break under a different
allocator). So strengthening the producer is the wrong fix.

A minimal failing demonstrator lives in PAL's own array test suite
(`pal/test/array_update/`): a field write through an arrayptr whose parent is
`array_pts_to_uninit` reports `Error 19: could not prove array_spec_initd`.

**Fix level is PAL translation + the `Pulse.Lib.C.Array` library** (not F*/Z3).
Candidate fixes (none free, deepest last): (1) **library borrow/return** — a
primitive that splits one uninit slot out of `array_pts_to` as a `ref T` with
`pts_to_uninit`, lets you fill its fields, and joins the initialized element
back, with PAL lowering a field write to a not-provably-`initd` slot through
*borrow → `$unfold-uninit` → per-field write → `$fold` → join* (mirrors the
stack-struct fill — recommended); (2) **write-fusion** — a PAL pass that fuses
consecutive field writes covering *all* fields of a fresh slot into one
`arrayptr_write` (fragile; breaks if writes are reordered or guarded); (3) a
**per-field init model** for struct elements plus an `arrayptr_write_field`
primitive (deepest). The C-surface escape hatch *today* is to assign the **whole
element** at once (`*slot = Mkelem ...;` → `arrayptr_write`, mask-only) instead
of field-by-field — but that changes the C body, which is disallowed for runtime
functions you may only annotate.

### 7.2 The `array_spec` API at a glance

An `array_spec T` is the pure (ghost) view of an array's contents that
`array_pts_to a p s` exposes. Core operations (all in `Pulse.Lib.C.Array`):

| Term | Meaning |
|---|---|
| `array_spec_len s : nat` | element count (the *spec* length; use this in `pure`, never `length_of`) |
| `array_spec_mask s i : prop` | slot `i` is allocated / in bounds |
| `array_spec_initd s i : prop` | slot `i` holds an initialized value |
| `array_spec_idx s i : T` | the value at slot `i` (needs `array_spec_initd s i`) |
| `array_spec_upd s i x` | functional update: `s` with slot `i` set to `x` |
| `array_spec_full_mask s` | every in-bounds slot is masked (allocated) |
| `array_spec_initialized s` | every in-bounds slot is initd |
| `array_spec_full s` | `full_mask /\ initialized` (a `full_array_spec`) |
| `array_spec_zeroed T n x` | the calloc view: length `n`, all slots initd to `x` |

Key SMTPat lemmas fire automatically (no manual call needed):

- `array_spec_upd_initd` / `array_spec_upd_mask` — `upd` makes slot `i`
  initd/masked and preserves every other slot's status.
- `array_spec_upd_idx1` — for `j <> i`, `array_spec_idx (upd s i x) j ==
  array_spec_idx s j` (the untouched-slots fact behind §10.12).
- `array_spec_zeroed_initd` / `_mask` — every slot of a `zeroed` array is initd
  and masked.

Slprop flavours: `array_pts_to a p s` (raw), `array_pts_to_full a p s` (`s` a
`full_array_spec`), `array_pts_to_uninit a s` (`= array_pts_to a 1.0R s ** pure
(array_spec_full_mask s)` — allocated but not initd), `array_pts_to_uninit' a`
(hides the spec, `[@@pulse_eager_unfold]`, §10.9), and `freeable_array a` (the
duplicable token `free_array` consumes).

## 8. Common errors quick reference

| Error | Typical cause | Fix |
|---|---|---|
| **12** | slprop where prop expected (or vice versa) | `_ensures` on a loop must be a pure prop; wrap pure props in slprop position as `_inline_pulse(pure (...))` |
| **19** | A VC reduces to `false` | Inspect the context dump; common culprits: break without `_ensures`, contradictory preconditions. If the goal is `array_spec_initd …`, you are field-writing an uninitialized struct array slot — see §7.1 |
| **76** | Statement returns non-unit but unit expected | Append `_ghost_stmt(())` after the statement |
| **228** | "Allocating a mutable local … expects an annotated post-condition" (loop cond can't read fields under an opaque inv), OR "Cannot prove X / In the context X" where the two print identically (§10.1), OR let-mut param-shadow drift (§6.5.1) | Add `[@@pulse_unfold]` to the loop inv; for the second re-run with `--print_full_names --print_implicits`; for the third strip the shadow (§6.5.1) |
| **240** | "Missing definitions in module X: f" on a downstream module **without** the failing line | Real per-line error hidden by F*'s splice-summary. Re-run with `--dump_module X` |
| **247** | Stale `.fsti.checked` after a helpers edit | `rm` the stale `.checked` files in `_cache/` |
| **321** | "Did not expect module Pulse.Main to be already checked" | Benign — a proofs-dir module that Pulse already provides cached |
| **339** | "Cannot infer implicit argument" | Provide the implicit explicitly, or refactor so the matcher has a syntactic anchor (hoist-existential pattern) |

When you see Error 19 with a "proof state" dump, read the `_if_hyp`, `_pure`
facts, and the goal carefully. The goal usually reveals which conjunct of an
invariant Pulse cannot re-establish at this program point.

### 8.1 Elevated z3rlimit for heavy quantifier-reasoning helpers

Helpers that discharge per-slot preservation across `array_spec` quantifiers
(e.g. memcpy/shift bridges proving a property for every element) often need an
elevated z3rlimit factor. Wire it as a target-specific override in the per-module
verify Makefile rule rather than globally:

```make
$(CACHE_DIR)/Func_<Name>.fst.checked: FSTAR += --z3rlimit_factor 16
```

### 8.2 `UInt32.div` SMT-friendliness

`FStar.UInt32.div a b` has a `Pure` ensures `v c == v a / v b` but **no SMTPat**,
so Z3 won't auto-trigger. Add an explicit pure assertion as the first ghost
statement after the read, bundling related bounds to give Z3 case-split hints:

```c
_ghost_stmt(assert pure (UInt32.v (FStar.UInt32.div a 2ul) == UInt32.v a / 2));
```

### 8.3 Diagnosing a failing or slow VC

When a function won't verify, **localize before you theorize**:

1. **Bisect with `assert pure (...)`.** Insert `_ghost_stmt(assert pure (P));`
   (or `assert (slprop);` in a ghost fn) at successive points. The first assert
   that fails is where your knowledge and Pulse's diverge; the last that passes
   tells you what is still in scope. This pinpoints *which* invariant conjunct is
   lost and *where*.
2. **Split a conjunctive goal.** If the failing VC is `P /\ Q /\ R`, assert each
   conjunct separately to find the guilty one — the dumped goal is often a big
   conjunction whose failing part is non-obvious.
3. **Isolate with a downstream `admit()`.** Put `_ghost_stmt(admit())` *after* the
   suspect point to confirm everything *before* it verifies, then move it earlier
   to bracket the failure. Remove every admit before declaring success.
4. **Identical-looking goal and context ⇒ implicit drift, not a missing fact.**
   Re-run with `--print_full_names --print_implicits` (§10.1) before adding a
   single lemma — you are usually one type-ascription away.
5. **Slow, not failing? Suspect structure first.** An opaque slprop hiding a
   `pts_to`, an existential keyed on the wrong name (§4 matcher), or a quantified
   invariant with a bad trigger. Only after ruling those out, raise the budget —
   prefer a *target-specific* `--z3rlimit_factor` (§8.1) over a global bump, and
   keep it as low as still passes.
6. **Flaky (passes sometimes)?** The proof is unstable — usually an
   under-constrained quantifier or a fragile trigger. Measure with `--quake 5`
   (or `--retry`), then stabilize: name intermediate facts with `assert pure
   (...)`, pin equality types (§10.1), or make a hot slprop opaque so the matcher
   can't wander. A stable proof is worth more than a fast one.
7. **Read the dump structurally.** In an Error 19/228 dump the `_pure` facts are
   your hypotheses, `_if_hyp` is the active branch condition, and the goal is the
   one thing Pulse can't close — map it back to a single invariant conjunct.

## 9. Spec design idioms

### Factor out reusable "shape" invariants

Wrap typedef bounds + structural invariants (monotonicity, sortedness, …) in a
`struct_inv v spec` pure prop. Layer per-context invariants on top:

```fst
let struct_inv  v spec    : prop = <typedef bounds> /\ sorted_at spec ...
let loop_inv_pure v spec k : prop = struct_inv v spec /\ valid_index_at spec k
```

Now `struct_inv` is reusable by every function that touches the struct.

### Bake stronger invariants into `_refine` when every function can re-establish them

The typedef `_refine` clause holds **invariantly across the entire lifecycle** of
every value of the typedef. Putting a strong invariant (e.g. sortedness) there is
sound *as long as every public function that takes the struct re-establishes it
on return*. Functions that transiently break it in their body are fine — once
they unfold the typedef pred they operate on raw `pts_to` / `array_pts_to_full`
and only need the invariant back at the `fold`/return boundary.

Bundling `struct_inv` into `_refine` beats threading
`_requires`/`_ensures(_inline_pulse(pure (struct_inv ...)))` through every caller
— fewer annotations, and Pulse picks the invariant up directly from the
auto-emitted `__pred`.

**The encoding.** Plain `_refine(<C expr>)` can only express bool conjuncts over
`this.<field>` / `this.<field>._length` projections. To call a hand-authored
helper (which can reference the typedef pred's spec parameter and return a
`prop`), drop into `_inline_pulse(...)` with a `(_slprop)` cast and call the
helper from inside `pure (...)`:

```c
_refine((_slprop) _inline_pulse(
    pure (Helpers_X.struct_inv this val_this_0.spec__elems_0)
))
```

Two things make this work:

1. **`(_slprop)` cast on `_inline_pulse(...)`** — the F*-flavoured cast PAL's
   C-frontend recognises here (alongside `(_specint)`). There is no `(prop)`. The
   cast embeds verbatim F* as an slprop directly without an implicit `with_pure`
   wrap; wrap the body in `pure (...)` to lift the `prop`-typed helper
   application to slprop position. It composes with the auto-emitted
   `Struct_X__pred ...` via `**`.
2. **`val_this_0` is in scope inside the inline body** — it is the spec parameter
   of the auto-generated `ty_X__pred` predicate. PAL only substitutes `this`;
   everything else resolves against the pred's bindings. Use it to reach spec
   fields like `val_this_0.spec__elems_0` (the ghost view of an array-typed
   field).

Gotchas inside `_inline_pulse(...)`:

- The body is **verbatim F***: you bypass `_specint` lifting, `._length` sugar,
  and the `&&`-vs-`**` overload. Write F* by hand: `FStar.UInt32.v`,
  `array_spec_len`, `/\` (not `&&`).
- F*'s `/\` cannot appear in a *plain* `_refine(...)` body — PAL would tokenize
  it as `/` followed by a stray `\`. Inside `_inline_pulse(...)` it is fine.
- **`<: nat` ascription** is needed when comparing `FStar.UInt32.v X` (type
  `uint_t 32`) to `array_spec_len S` (type `nat`) in an inline conjunct —
  otherwise F* picks `uint_t 32` for both sides and fails the rhs subtype check.
  Not needed inside a standalone helper definition (it picks `prop` for `==`).

**When NOT to use this.** If even one function in the API genuinely cannot
re-establish the bundled invariant on return (legacy mutators, partial-update
setters), keep it free-standing and thread contracts explicitly. Don't trap
yourself by baking it into `_refine`.

### Inline `_refine` vs. a `Helpers_<TYPE>.fst` file for typedef invariants

Decide where a typedef invariant lives by its weight:

- **Inline `_refine((_slprop) _inline_pulse(pure (...)))`** when the invariant is
  a few short pure conjuncts — keeps the C header self-contained and the predicate
  visible at the declaration.
- **A separate `Helpers_<TYPE>.fst`** when the invariant is multi-line, **branches
  on a field** (e.g. an inline-vs-heap case split), references a **spec
  parameter**, or is **reused by helper lemmas**. Name the predicate once and
  refer to it from both the `_refine` and the proof lemmas: the two stay in sync,
  and the name (not an anonymous slprop) shows up in goals and error messages.

### Suppressing the auto-generated typedef pred with `_plain`

Sometimes the auto-generated typedef pred (with its single existentially
quantified spec parameter) doesn't fit the struct's ownership discipline. The
canonical case is a **small-vector**: an array field aliases an inline by-value
array of the same element type (the `CONTAINER` running example: `Elems` points
into `Inline[N]` *or* a heap allocation, selected by `Capacity`).

The auto pred would unconditionally provide
`array_pts_to_full this.elems p val.elems_0` and say nothing about the aliasing
between `this.elems` and `this.inline`. **`_plain` on a typedef** suppresses
PAL's auto-generated `Struct_X__pred` call; the custom
`_refine(_inline_pulse(...))` body becomes the *whole* predicate, and the spec
parameter is dropped from the pred signature (call sites become
`ty_X__pred (!var_x) p`, no spec arg). Factor the body through one slprop helper:

```c
_refine(_inline_pulse(Helpers_X.struct_inv $(this) p))
_plain
typedef struct CONTAINER { ... } CONTAINER;
```

```fst
// Declare `unfold` so the pred's [@@pulse_eager_unfold] propagates to use sites.
unfold
let struct_inv (this: SX.struct_container) (p: perm) : slprop =
    pure (field_bounds this) **
    (if UInt32.v this.SX.struct_container__capacity <= inline_cap
     then
       // Inline branch: Elems aliases the by-value Inline field directly —
       // no existential; feed `this.inline` straight to array_pts_to_full.
       CA.array_pts_to_full this.SX.struct_container__elems p
                            this.SX.struct_container__inline
     else
       // Heap branch: existential spec view + freeable_array token so
       // free/grow/shrink can discharge free_array. `emp` in the inline
       // branch correctly forbids freeing the inline alias (UB).
       exists* (heap_arr: CA.full_array_spec ty_elem).
         CA.array_pts_to_full this.SX.struct_container__elems p heap_arr **
         CA.freeable_array this.SX.struct_container__elems **
         pure (CA.array_spec_len heap_arr
                 == UInt32.v this.SX.struct_container__capacity))
```

Things to know:

1. **`p` and `this` are both in scope** inside the verbatim body (the pred's
   parameters). Use `p` directly; use `$(this)` / `$(this.<field>)` for
   substitution.
2. **No `(_slprop)` cast** needed when the body returns an slprop directly —
   `_inline_pulse` parses it in slprop position.
3. **Conditional permissions** (heap-vs-inline, optional fields, …): express the
   dependency directly with an `if-then-else` over slprop branches, as above. The
   branches typically carry different ownership shapes. `freeable_array` is
   internally `pure (is_full_array r)` and so duplicable — safe inside a pred
   held at fractional perm; sites that free rely on `unfold` (both pred and
   helper are `unfold`) to expose the branch and case-split.
4. **`uninit_pred` becomes `emp`** with `_plain`. If functions need uninit access
   through the typedef (`_out_` params), provide it manually via `_inline_pulse`
   in the function spec.
5. **All call sites regenerate automatically** — PAL drops the spec parameter
   wherever the typedef appears. After adding `_plain`, run `make translate` then
   re-verify.
6. **Existential vs spec-parameter trade-off.** With `_plain` you lose the spec
   parameter; callers can't easily talk about contents without `unfold`ing the
   pred. If you only need to *add* pure invariants on top of the auto-pred, use
   plain `_refine((_slprop) _inline_pulse(pure (...)))` (no `_plain`) — keeps the
   spec parameter, just layers constraints. Use `_plain` only when you need to
   *replace* the auto pred (aliasing, custom permission shapes).

Reference example: PAL's own `test/refine_typedef_pred/`.

### Refine the *pointer*, not the struct, for pointer-keyed APIs

For a struct whose ownership shape depends on runtime data (like the small-vector
above), an alternative to `_plain` on the struct is a separate typedef for the
**pointer**:

```c
_refine((_slprop) _inline_pulse(Helpers_X.obj_inv $(this) p val_this_0))
typedef CONTAINER* obj_ptr;
```

`obj_inv this p s` then describes what it means to *hold a pointer to the struct*:
`pts_to`s for each scalar/handle field, an `array_pts_to` for the array field,
plus an opaque case-split for the conditional ownership (§10.2).

Advantages over `_plain` on the struct typedef:

1. The inline storage is **not** part of the pointer's ownership — the struct
   still carries it as a by-value field, but `obj_inv` doesn't double-count it.
2. Most of the API (which takes a pointer) gets a clean
   `(var_obj: ty_obj_ptr) requires ty_obj_ptr__pred var_obj 1.0R val_obj_0`
   shape, with `val_obj_0` carrying the spec view.
3. The struct typedef's auto-generated pred stays intact — useful for an
   initializer that constructs the struct by value.

### Co-design caller and callee specs

The generated `Func_Callee.fsti` *is* the contract every caller sees — callers
never look inside the callee body. So when a caller can't prove something about a
callee's result, **the fix is almost always in the callee's spec, not the
caller's body**:

- **Caller needs a fact the callee doesn't promise ⇒ strengthen the callee's
  `_ensures`.** Add the missing postcondition to the callee, re-verify the
  *callee* (it must actually re-establish it), then the caller gets it for free.
  Don't try to reconstruct the fact in the caller — you usually can't, because the
  callee's internals are abstracted away.
- **Callee's `_requires` is too strong for a legitimate caller ⇒ weaken it.** If a
  precondition rules out a call the caller can't satisfy (and the callee doesn't
  truly need it), relax the callee's requires rather than bending the caller.
- **Symmetric danger: an over-strong `_ensures` the callee can't actually
  re-establish.** If you strengthen a post and the *callee* now fails, you asked
  for more than the code provides — weaken back to what's true.

Iterate at the boundary: tighten/loosen one clause, re-verify the callee in
isolation (single-file loop, §2), then re-verify the caller. Treat the `.fsti` as
the negotiated interface between the two proofs.

### Prefer semantic constraints to over-approximations

Capture the *actual* constraint, not a stronger sufficient one. E.g. instead of
`Capacity ≤ INT32_MAX` (to keep `Head + Size` from overflowing `uint32`), write
`Head + Size ≤ UINT32_MAX` — strictly weaker and exactly the property needed.

### Machine-integer reasoning and overflow VCs

PAL lowers a C arithmetic op on a fixed-width integer to the corresponding checked
F* operation — e.g. `a + b` on `uint32_t` becomes `FStar.UInt32.add a b`, whose
precondition is `UInt32.v a + UInt32.v b <= FStar.UInt.max_int 32`. **Each such op
emits an overflow VC** at that program point; you discharge it from bounds carried
in `_requires`, `_invariant`, or the typedef `_refine`.

- **Project to math with `.v`.** `FStar.UInt32.v x` (type `uint_t 32`, i.e. a
  bounded `nat`) is the mathematical value; do all reasoning over `.v` and the
  named bounds (see "Use named F* constants" below).
- **Ghost arithmetic that can't overflow: use `_specint`.** Casting a C expression
  with `(_specint)` lifts it to unbounded mathematical `int`, so *no* overflow VC
  is generated — use it for index/length math inside annotations that is provably
  in range but whose intermediate sums would trip the machine bound.
- **Mixed-width comparisons need ascription.** Comparing `FStar.UInt32.v x`
  (`uint_t 32`) to a `nat` such as `array_spec_len s` inside an inline conjunct
  needs `(... <: nat)` (§9 `_refine` encoding) so F* picks the common supertype.
- **No SMTPat ⇒ assert the result.** Division/modulus and a few other ops have
  `Pure` specs without SMTPats; surface the result with an explicit
  `assert pure (...)` (§8.2).

### Use named F* constants

| Use this | Not this |
|---|---|
| `FStar.UInt.max_int 64` | `pow2 64 - 1` |
| `x + y <= FStar.UInt.max_int 64` | `x + y < pow2 64` |
| `FStar.Int.max_int 32` (INT32_MAX) | `pow2 31 - 1` |
| `FStar.UInt.max_int 32` (UINT32_MAX) | `pow2 32 - 1` |
| `FStar.Int.min_int 32` (INT32_MIN) | `- pow2 31` |

In C annotations use `INT32_MAX` / `UINT32_MAX` from `<stdint.h>`. In
`_inline_pulse(pure (...))` use the F*-side `max_int`/`min_int` forms.

## 10. Pulse matcher pitfalls and the case-split fold pattern

### 10.1 Hidden-implicit drift: when two identical-looking slprops won't unify

**Symptom.** Pulse Error 228 of the shape:

```
Cannot prove:    foo a b c
In the context:  foo a b c
```

where context and goal are **character-for-character identical**, yet Pulse
refuses to discharge.

**Root cause.** F* elides implicit arguments when pretty-printing. Two terms that
print identically can differ in an elided implicit. The usual culprit is the
implicit type of `Prims.eq2` inside a `pure (X == Y)` slprop: when `==` relates
values of different-but-compatible types — e.g. `array_spec_len ... : nat` on the
LHS and `UInt32.v ... : uint_t 32` on the RHS — F* computes the *least upper
bound* to pick the implicit, and the LUB depends on the surrounding inference
context (definition site vs use site vs `rewrite` RHS each pick differently).

**Diagnostic.** Re-run with `--print_full_names --print_implicits`. The differing
term becomes visible in both goal and context.

**Primary fix.** Pin the equality to a single canonical type **in the slprop
definition**:

```fst
// Before:  pure (CA.array_spec_len s == UInt32.v cap)
// After:   ascribe RHS to nat so every unfolding produces eq2 #nat
pure (CA.array_spec_len s == (UInt32.v cap <: nat))
```

**Secondary fix.** Avoid `rewrite p as q` where `p`/`q` are large slprops
containing such equalities — every RHS re-elaboration is a fresh chance to pick a
different LUB. Prefer **parameterised intro helpers** (§10.3) that elaborate the
slprop exactly once at the call site.

### 10.2 Opaque case-split slprops for conditional ownership

When a predicate's ownership depends on a runtime boolean (inline-vs-heap, …),
an `if b then p else q` inside the body works for *concrete* `b` (Pulse
iota-reduces) but fails for *symbolic* `b`: Pulse rewrites it as
`match b with true -> p | _ -> q` and the matcher can't traverse the match form.

Introduce an opaque `case_split` slprop — transparent definition but marked
`[@@"opaque_to_smt"]` so the matcher won't unfold it for symbolic `b` — and
provide reveal lemmas:

```fst
[@@"opaque_to_smt"]
let case_split (b: bool) (p q: slprop) : slprop = if b then p else q

let case_split_true_eq  (p q: slprop) : Lemma (case_split true  p q == p)
  = reveal_opaque (`%case_split) (case_split true  p q)
let case_split_false_eq (p q: slprop) : Lemma (case_split false p q == q)
  = reveal_opaque (`%case_split) (case_split false p q)
```

**Do not** use `assume val case_split` + `assume`-bodied equalities — it adds
trusted axioms for no benefit. The `opaque_to_smt` + `reveal_opaque` form is
identically opaque to the matcher but discharges the equalities by reveal + iota.

### 10.3 Generalised `btrue`/`bfalse` intros and elims

`rewrite p as q` re-elaborates `q` in a fresh context, re-triggering §10.1.
Provide generalised variants that take the boolean as a parameter and a
`pure (b == true/false)` precondition — the inner slprops elaborate exactly once
at the call site:

```fst
ghost fn intro_case_split_btrue (b: bool) (p q: slprop)
  requires p ** pure (b == true)
  ensures  case_split b p q
{ intro_case_split_true p q; rewrite (case_split true p q) as (case_split b p q); }

ghost fn elim_case_split_btrue (b: bool) (p q: slprop)
  requires case_split b p q ** pure (b == true)
  ensures  p
{ rewrite (case_split b p q) as (case_split true p q); elim_case_split_true p q; }
// symmetric: ..._bfalse
```

Use `_btrue`/`_bfalse` everywhere a discharge `pure (b == true/false)` is
available — strictly easier on the matcher than the concrete-bool form plus a
manual `rewrite`.

### 10.4 Branched fold helpers for case-split predicates

Suppose `obj_inv this 1.0R s := ... ** case_split (UInt32.v s.capacity <= N) (inline_eq) (heap_eq) ** ...`.
A single monolithic fold helper that takes both branches as `case_split b ...`
forces the caller to construct that slprop ahead of time — defeating the point.
Instead **split into one helper per branch**, each taking the active-branch
ownership as a plain slprop and constructing the case-split internally:

```fst
ghost fn fold_inline (this) (s: erased obj_spec)
  requires <all unfolded pts_to's and pures of obj_inv MINUS the case-split>
        ** pure (UInt32.v s.capacity <= N /\ s.elems == inline_of this)
  ensures  obj_inv this 1.0R s
{
  intro_case_split_btrue (UInt32.v s.capacity <= N)
    (pure (s.elems == inline_of this))
    (CA.freeable_array s.elems ** pure (...));
  // ensures unfolds obj_inv via [@@pulse_unfold]; all conjuncts now match
}
// symmetric: fold_heap
```

### 10.5 Thick wrapper ghosts + `#X: erased T` for tiny C bodies

The C body should not do field rewrites, post-spec construction, or case-split
elimination — that scaffolding belongs in Pulse. Write a **thick wrapper** per
branch that takes the typed `this: ref struct_X` and an *implicit* erased
pre-state:

```fst
ghost fn reset_inline
      (this: ref SX.struct_container)
      (#val_pre: erased obj_spec)             // implicit: PAL need not pass it
  requires <unfolded body of obj_inv at val_pre, with the mutated field updated>
        ** pure (UInt32.v val_pre.capacity <= N)   // active branch condition
  ensures  exists* (s_post: obj_spec). obj_inv this 1.0R s_post
{
  let s_post = hide ({ reveal val_pre with count = 0ul });
  rewrite each (reveal val_pre).elems    as (reveal s_post).elems;
  rewrite each (reveal val_pre).elems_0  as (reveal s_post).elems_0;
  rewrite each (reveal val_pre).capacity as (reveal s_post).capacity;
  rewrite each 0ul                       as (reveal s_post).count;
  elim_case_split_btrue ...;
  fold_inline this s_post;
}
```

The C body collapses to:

```c
_ghost_stmt(unfold Helpers_X.obj_inv);
Obj->Count = 0;
if (Obj->Capacity <= N) { _ghost_stmt(Helpers_X.reset_inline $(Obj)); }
else                    { _ghost_stmt(Helpers_X.reset_heap   $(Obj)); }
```

PAL infers the implicit `#val_pre` from the slprop context — no special syntax
needed.

### 10.6 Ghost `if` cannot branch on a Ghost-typed bool

In a `ghost fn`, `if (UInt32.v (reveal s).capacity <= N) { ... } else { ... }`
fails Error 76 (`Expected a Total computation, but got Ghost`): `reveal` is
Ghost, and `if` demands Total. **Workaround**: split into two functions — one per
branch, each taking a `pure (b == true/false)` precondition — and push the
branching back to the caller (the C body or a non-ghost helper) that has a
concrete bool.

### 10.7 `with x. _` requires exactly one `exists*` in the goal

`with x. _;` binds the witness of *the* existential currently in the goal. If the
goal has zero (Pulse already auto-opened the existential on function entry — e.g.
from `requires exists* (val_pre: ...). body` in the signature) or multiple
existentials, it fails: "Binding names with a wildcard requires exactly one
existential quantifier in the goal."

Common cause: writing `requires exists* (val_pre: ...). body` expecting to name
`val_pre` in the body — but Pulse already opened it and `val_pre` is *not*
accessible (the name scopes to the requires clause only). **Solutions:**

1. Take `val_pre` as an `(#val_pre: erased T)` implicit (recommended — §10.5).
2. Take it as an explicit `(val_pre: erased T)` argument; caller passes `_`.
3. If multiple existentials are genuinely in the goal, name each:
   `with x y z. assert (p x y z)`.

### 10.8 Workflow: when a thick fold helper won't verify

1. **Look for `eq2` drift first** (§10.1) — run with `--print_implicits`. Pin
   every problematic equality to a canonical type via `<: T` at the *definition*
   site, then refer to that single elaborated form everywhere.
2. **Move `rewrite p as q` to a parameterised intro** (§10.3) — keeps the slprop
   literal out of the use-site re-elaboration path.
3. **Split per branch** (§10.4) — never one helper that does both branches; each
   takes the active-branch ownership in its requires.
4. **Take the pre-spec as `#X: erased T`** (§10.5) — lets PAL call it with no
   special syntax and gives the helper a stable pre-state name without `with`/
   `exists*` gymnastics.
5. **Build `s_post = hide ({ reveal X with field = new_value })`**, then
   `rewrite each (reveal X).f as (reveal s_post).f` for each preserved field plus
   one for the mutated field. The case-split's discriminator gets rewritten
   transparently with the field rewrites.
6. **Then call the narrow per-branch fold helper** with `s_post`.

### 10.9 Consuming an eager-unfold uninit array in a helper precondition

`array_pts_to_uninit' a := exists* y. array_pts_to_uninit a y` is
`[@@pulse_eager_unfold]`. When it appears in a function's context, Pulse opens
the existential *eagerly on entry* — the witness binds to a fresh name with no
stable handle.

**Wrong**: trying to bind it in the body with `with x. _;` — by then the
existential is already opened (Error: no existential in context).

**Right**: take the witness as an `#X: erased ...` implicit on the helper and have
the helper consume `array_pts_to` directly:

```fst
ghost fn fill_fold
      (this: ref SX.struct_container)
      (#val_pre: erased (CA.array_spec ty_elem))
  requires ... ** CA.array_pts_to (inline_of this) 1.0R val_pre ...
{
  let s_post = hide ({ ...; elems_0 = reveal val_pre; ... });
  rewrite each (reveal val_pre) as (reveal s_post).spec__elems_0;
  ...
}
```

The caller holds `array_pts_to_uninit'`; Pulse unfolds it at the call and unifies
the auto-bound witness against the `#val_pre` implicit; the
`with_pure (array_spec_full_mask y)` half drops away as `emp`-equivalent.

### 10.10 Weaken the invariant instead of adding axioms

When a desired invariant needs a fact that *should* be provable from the
underlying API but no public lemma exposes it, you have two choices:

1. **`assume val` a linkage lemma** — adds a trusted axiom. Avoid unless truly
   necessary.
2. **Weaken the invariant** so the missing fact isn't required, then verify
   downstream uses don't actually need it.

Example. An invariant asserting `UInt32.v capacity <= array_spec_len elems_0`
(to bound array writes) may be unprovable because the only lemma tying a handle's
`length a` to its spec view's `array_spec_len y` isn't re-exported through the
public array interface. Rather than `assume val length_eq_spec_len`, drop the
constraint from the invariant if every consumer can do without it (e.g. readers
only index `i < Count`, and a per-slot-validity predicate already gives
`array_spec_initd` for each such `i`). **Heuristic.** Before reaching for
`assume val`, audit which call sites actually consume the constraint. If none of
the verified ones do, weakening is the right move — zero axioms added.

### 10.11 `arrayptr_pts_to` is pure facts; surface them with `arrayptr_pts_to_facts`

`arrayptr_pts_to x y` is a **transparent** `let` =
`pure (base_of x == base_of y /\ length x == 0)`. Two consequences:

1. **It is duplicable, not linear.** It carries no permission — just a witness
   that `x` is a zero-length pointer sharing `y`'s base. Use
   `_preserves(_inline_pulse(arrayptr_pts_to $(p) $`arr))` (it survives writes
   through the parent).
2. **The carried facts are framed away unless extracted.** Folded,
   `base_of x == base_of y /\ length x == 0` is invisible to Z3. Call the ghost
   lemma `arrayptr_pts_to_facts x` (preserves `arrayptr_pts_to x y`, ensures the
   pure facts) to surface both — in particular `length x == 0`, otherwise trapped
   inside the folded predicate.

**`array_is_null` typing.** `array_is_null r : b:bool { b <==> r == array_null }`.
Always compare via `pure (array_is_null r)` / `pure (not (array_is_null r))` —
never `array_is_null r == true` / `== false`. The `==`-to-`bool` form
re-introduces a `match … with | true -> … | _ -> …` the matcher won't normalize
under a uvar (the §13.1 disjunctive-post trap).

### 10.12 Tear/seal: in-place mutation of one array slot under a refined-pointer invariant

To mutate **one element** of an array embedded inside an opaque refined-pointer
invariant (§9 "Refine the pointer"), you cannot just open the invariant and
write — it asserts a *structural* fact over the array (e.g. "every live slot is
valid") that is momentarily false while the slot is half-written. The pattern:
define a **torn mirror** that *exempts one index*, tear into it, mutate, seal back.

For `obj_inv this p s` whose array invariant is `elems_valid_of used elems_0`
(`forall i < used. slot_valid i`):

1. **Weaker "except" predicate.**
   `valid_except used s except := forall i < used. i <> except ==> slot_valid s i`.
   Keep it `[@@opaque_to_smt]` with a pointwise eliminator (`valid_except_get`)
   and a `forall`-intro (`valid_except_intro`).
2. **Torn invariant.** `obj_inv_torn this p s except` = a copy of `obj_inv` with
   `elems_valid_of` replaced by `valid_except … except` (everything else — the
   `pts_to`s, the raw `array_pts_to`, `array_spec_full_mask`, the case-split — is
   identical). Also opaque.
3. **Tear** (`obj_inv_tear`, `requires obj_inv … ensures obj_inv_torn … except`):
   unfold the full inv, apply `valid_of_implies_valid_except`
   (valid-everywhere ⟹ valid-except-one), fold the torn inv. Always sound.
4. **Mutate slot `except`.** Either a whole-element `arrayptr_write` (mask-only —
   works even on an uninit slot, modulo §7.1 for *field* writes) or an
   `array_spec_upd`. The spec-level core is `valid_except_upd_at_except`:
   overwriting *exactly* the exempt slot preserves `valid_except` for the others
   (`array_spec_upd_idx1`/`array_spec_upd_initd` fire by SMTPat — the other slots
   are untouched).
5. **Seal** (`obj_inv_seal`,
   `requires obj_inv_torn … except ** pure (except < used /\ array_spec_initd s except /\ <per-slot bounds at except>) ensures obj_inv …`):
   unfold torn, apply `valid_except_seal` (= `valid_of_intro` discharging the
   `i == except` case directly and every other `i` via `valid_except_get`), fold
   the full inv. The `initd` + bounds premise is exactly what you re-establish by
   filling the slot.

Why a *mirror* rather than parameterising the original by `except`: keeping
`obj_inv` unparameterised means the many readers/initializer callers never see
`except`; only the mutators pay the tear/seal cost. The torn predicate and its
three lemmas (`valid_of_implies_valid_except`, `valid_except_upd_at_except`,
`valid_except_seal`) are the entire reusable machinery.

### 10.13 Per-arm eliminators for a case-split (disjunctive) function post

A function whose result shape depends on a runtime test (e.g. a "reserve" routine
that returns either a NULL slot on alloc failure or a non-NULL carved slot) is
most cleanly specified with a **single opaque case-split atom** as its post, then
**consumed via per-arm ghost eliminators** — the consumer-side complement of
§13.1's producer-side `introduce`.

```fst
let reserve_post this v_pre ret val_post idx_post : slprop =
  case_split (array_is_null ret)
    (reserve_true_arm  this v_pre val_post idx_post)   // NULL: inv unchanged
    (reserve_false_arm this v_pre ret val_post idx_post) // non-NULL: torn inv + slot ptr
```

Provide one eliminator per arm, each taking the discriminating `pure` fact in its
`requires`:

```fst
ghost fn reserve_elim_null    ... requires reserve_post ... ** pure (array_is_null ret)
                                  ensures  obj_inv this 1.0R val_post ** pure (val_post == v_pre /\ ...)
ghost fn reserve_elim_nonnull ... requires reserve_post ... ** pure (not (array_is_null ret))
                                  ensures  obj_inv_torn this 1.0R val_post idx_post
                                        ** arrayptr_pts_to ret val_post.elems ** pure (...)
```

Each body is
`unfold reserve_post; elim_case_split_btrue/_bfalse …; unfold <arm>; <unfold the arm's inner op>`.
The caller does
`if (array_is_null Slot) { ...elim_null...; return NULL; } else { ...elim_nonnull... }`
and each branch gets a clean, non-disjunctive slprop with no uvar gymnastics.
Pair the non-NULL arm with §10.12: it hands back a **torn** invariant exactly so
the caller can fill the carved slot and reseal.

## 11. Workflow / habits

1. **Read the C code first.** Identify ownership: which pointers are arrays,
   consumed, out-params, or must stay live across a loop. Add ownership
   annotations (`_array`, `_consumes`, `_out`, `_plain`) before any functional
   spec — wrong ownership produces a cascade of admits no spec can fix.
2. **Triage admits after translating.** `grep -rn '(admit())' build/...` — every
   hit is a construct PAL couldn't translate. Check any `TranslationErrors.fst`
   and diagnostics output. **Ignore** expected axiomatized plumbing
   (`assume val …__aux_raw_*`, `…__pred`) — these are not failures.
3. **Iterate on a single F* file**, not full `make`, between edits.
4. **Open the generated `.fst` after every PAL change.** Read the generated
   `requires`/`ensures`/body to see what Pulse must prove — unambiguous C
   annotations can generate surprising F*.
5. **Don't blindly bump rlimits on a timeout.** Diagnose the structural issue
   first (hoist an existential, change opaqueness, restructure the invariant);
   nearly every "long proof" has a cheap structural fix.
6. **Never modify C runtime function bodies** unless explicitly authorized. Add
   only erased annotations, `_ghost_stmt` calls, and spec clauses.
7. **Keep helpers in `Helpers_*.fst`**, not inline in C. Small, descriptive
   `let`/`ghost fn` names — they appear in goals and error messages.
8. **Get an independent critique before non-trivial invariant changes.** Pulse
   matcher behaviour is subtle, and a bad invariant shape can cost hours.

## 12. Where to look for examples

- PAL's own test suite (`pal/test/<topic>/<topic>.c`) is the canonical source of
  annotation patterns; generated F* lives in `pal/test/<topic>/out/`. Useful
  topics: `break_continue` (break/continue loops), `compound_ops` (`++`/`--`),
  `arrayptrs` (arrayptr handling), `array_update` (whole-element vs single-field
  element writes, incl. the uninit-slot failing demonstrator — §7.1),
  `refine_typedef_pred` (`_plain` typedef pred), `dpe` (richer typedef
  refinements with `_refine_value`).
- PAL's Pulse syntax reference (`pal/pulse/syntax.md`).
- F* standard library (`FStar.Int.*`, `FStar.UInt.*`, `FStar.Seq.*`,
  `FStar.Classical.*`) for integer bounds, sequences, and classical-logic
  combinators.

## 13. Manipulating existentials (early returns + disjunctive posts)

`exists*` postconditions are auto-introduced by Pulse's matcher creating uvars
and solving them. This breaks down in two common situations.

### 13.1 Disjunctive post with `if-then-else` and early `return`

If a function's post is
`exists* val_post. (if cond_on_return then sl_failure else sl_success) ** ...`
and the body has `return array_null` (or similar) inside a nested branch, Pulse
tries to discharge the post with `cond := array_is_null array_null`. The matcher
cannot reduce `match array_is_null array_null with | true -> A | _ -> B` to `A`,
even though it is definitionally `true`, because the witness for `val_post` is
still a uvar.

**Fix.** Before the early `return`, **explicitly introduce the existential with
the failure witnesses**:

```c
_ghost_stmt(introduce exists* (val_post: Helpers_X.obj_spec) (idx_post: nat).
              (if Pulse.Lib.C.Array.array_is_null array_null
               then Helpers_X.obj_inv var_obj 1.0R val_post
                 ** pure (val_post == reveal var_val_pre /\ idx_post == UInt32.v var_index_pre)
               else <success>)
              ** pure (idx_post == UInt32.v val_index_0)
            with var_val_pre (UInt32.v var_index_pre));
return NULL;
```

Once witnesses are explicit, the `match` reduces and the matcher only has to match
`obj_inv var_obj 1.0R var_val_pre` against the context. For the **consumer** side
— eliminating such a disjunctive post in the *caller* via per-arm ghost helpers —
see §10.13.

### 13.2 Eliminating an existential to give it a name (`with x. assert ...`)

When the context contains `exists* x. p x` and the next operation must refer to
`x` by name (pass it to a ghost helper, satisfy a pure equation):

```pulse
with w. assert (p w);   // binds w : erased _, brings p (reveal w) into context
```

This is the eliminator for `exists*`. Common uses: after unfolding a slprop with
an existential, name its witness before calling a helper; after a function call
whose post is `exists* val_post. ...`, name `val_post` to pin it. **Gotcha**
(§10.7): `with x. _` (anonymous body) requires *exactly one* `exists*` in the
goal; if multiple, name each.

### 13.3 Introducing an existential with explicit witnesses

When the post has an `exists*` whose witnesses Pulse can't infer (opaque slprops,
`match`/`if` discriminants on uninferrable values, syntactic context mismatch),
provide them explicitly:

```pulse
introduce exists* x1 ... xn. p with w1 ... wn;
```

This *replaces* the matcher's uvar guess with the supplied terms; the matcher
then only discharges `p[w1/x1, ...]`.

### 13.4 Pattern combinator: name-then-introduce

`with v. assert q v; introduce exists* x. p x with v;` re-packages a context-form
existential into a goal-form existential when the two shapes differ but the
witness mapping is the identity (or a simple expression in `v`). Useful when the
context has `exists* v. q v` (e.g. from a call's post) and the goal needs
`exists* x. p x` (the enclosing function's post).

### 13.5 When to reach for explicit existentials

Default: let the matcher auto-introduce. Reach for explicit
`introduce exists* ... with ...` when you see:

- **Error 228 "Cannot prove `match cond with | true -> X | _ -> Y`"** where
  `cond` is definitionally `true`/`false` but Pulse can't normalize it under a
  uvar.
- **Error 339 "Cannot find witness"** for a post-condition existential.
- **Error 228 with a `(*?u…*)_` uvar** in the unprovable goal — Pulse failed to
  pick a witness.

Reach for `with v. assert ...` when a helper call needs to refer by name to a
witness the previous step existentialised, or when an `_ghost_stmt(unfold X)`
opened an `exists*` and the next step needs the witness.
