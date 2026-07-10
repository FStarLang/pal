# Proving C with PAL (Proof Annotated Language for C) + F*/Pulse

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

## 3. Ideal workflow

### 3.1 Understanding the problem
First, understand the C code you are analyzing and the properties you want to prove about it. Ask the user if needed for clarification on whether the target is memory safety or full functional correctness.
### 3.2 Phase 1: Translation
Next, having identified the target of verification, first use PAL to only translate the relevant C code into F*. This may generate some `admit()` calls for the features that PAL does not yet support. Report these admits to the user before beginning any verification work.
### 3.3 Phase 2: Verification
Next, analyze the verification target function by function. Identify the easiest entry point and narrow down the scope of the verification to that function first. Functions that operate on complex data structures such as structs and unions often require invariants on these structures first. Add these invariants using the appropriate annotation syntax before starting with verifying the function.
When verifying a function, start with the simplest spec and gradually increase the complexity as you gain confidence in the proof. Latter parts of the guide give information on writing good specifications and guidelines for progressing the proof by defining and applying helper lemmas.

### 3.4 Extremely Important Guidelines
- DO NOT MODIFY THE C CODE UNLESS EXPLICITLY ASKED: Our goal is to modify the C code as is. Therefore, do not change the C code for verification unless the user explicitly asks.
- BE AWARE OF BUGS: Often times verification might be stalled due to bugs in PAL or Pulse. In these cases STOP and report the error to the user instead of struggling ahead.


## 4. Writing Specifications
Stating the correctness of C code involves stating the specification for functions as annotations in the C code. These annotations encode the pre and postconditions for the functions. Additionally, PAL annotations can also be used to state invariants on data types such as structs, unions, typedefs etc. Finally, all loops in the C code need to be annotated with appropriate loop invariants. (Loop invariants and if-ensures are discussed in 6)

### 4.1 Differentiating between raw pointers and arrays
The first step in writing specifications is to use the `_array` and `_arrayptr` annotations for differentiating between type pointers and arrays. PAL by default treats all pointers as references, the `_array` and `_arrayptr` tags tell PAL to treat them as arrays and array pointers, respectively. For more information on how arrays are modelled in PAL, refer to the documentation in the PAL repo.

The second step can be either to add the type invariants or to write the function specifications. Suppose the module under consideration heavily involves passing around and modifying a complex data structure then first write the invariant for that data structure. Both of these involve writing accompanying Pulse code. First, we take a look at best practices for writing such code.

### 4.2 Writing Pulse code used in function definitions
Writing specifications often involves writing pure pulse code for definitions and possible accompanying unfolding and folding lemmas. These definitions and accompanying lemmas must be stated in a separate helper file.

Every custom slprop definition that you add needs to either be declared auto unfold or have associated unfolding and folding lemmas. Use `[@@pulse_unfold]` / `[@@pulse_eager_unfold]` tags
for slprop definitions you want Pulse to silently unfold at use sites.
Without one of these, loop-condition reads (e.g., `obj->Count > 0`) fail with
**Error 228** because the opaque slprop hides the `pts_to`.

However, sometimes making definitions auto unfold can lead to performance issues or make the proof more difficult to manage. In such cases, it might be better to explicitly unfold the slprop at specific points in the code. An example:

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

### 4.3 Writing struct invariants
When writing struct invariants, first deeply understand the logical invariant that should hold. Search for the strongest property that is maintained by all the functions. This property may have some pure components and some ownership information. Define these components separately and then define a final slprop combining these two parts. Finally associate the invariant with the data type by using the `_refine` annotation. For more information on `_refine`, see the documentation in the PAL repo.

### 4.4 Annotations for functions
The last step in adding specs is to add each function's pre- and post-conditions using the appropriate annotations. Note that PAL by default generates, for every function argument, a precondition requiring full ownership of that argument and a postcondition returning that ownership. In many cases this is a sufficient spec for the memory-safety property. However, in many other cases this contract is too strong. In these cases, each argument can be prefixed with a `_consumes`, `_out`, or `_plain` tag. The `_consumes` tag instructs PAL to require ownership of the argument but not return it; the `_out` tag instructs PAL to require only *uninitialized* storage for the argument (a `pts_to_uninit` precondition) and return it initialized (a `pts_to` postcondition); and the `_plain` tag instructs PAL not to generate any ownership annotations for that argument. These tags must only be used when the default is truly too strong for the function.
In the case that `_plain` truly has to be used, custom pre and post conditions can be added using the `_requires` and `_ensures` annotations.

### 4.5 Importance of readable specification
A good specification is not just the most precise one but also a readable and accessible one. To that end, never use numeric constants directly in the specifications. Instead use named constants to express the maximum values for each type. These are easily available in F* as well as in the header exported by PAL.


## 5. Progressing the Proof
PAL is an automated tool and ideally proofs should be generated automatically. However, in many cases, manual intervention is often required to guide the proof. Remember that proving is an iterative process and may require changing the approach or adding more detailed specifications.

To manually help along the proof, you can 
(1)define additional lemmas and apply them by using `_ghost_stmt(...)` in the C function body, 
(2)insert the right asserts and 
(3) do manual rewrites using `_ghost_stmt(rewrite x as y in ...)`.
Doing any of this requires understanding the methods PAL provides for referring to the variables in the code.

### 5.1 Antiquotation inside `_inline_pulse(...)`
For the full antiquotation reference — `$(expr)`, `$&(expr)`, `$type`, `$field`, `` $`tick ``, `$declare`, and the `$fold` / `$unfold` families — see the **Antiquotation** section of [`pal_surface_syntax.md`](pal_surface_syntax.md).

Pulse ghost-fn body syntax you will write inside `_ghost_stmt(...)`:

- `let x = e;` (statement form, semicolon, **not** `let x = e in`).
- `fold (P args)` / `unfold (P args)` — must include args, not a bare name.
- `rewrite slprop1 as slprop2` — spatial rewrite using a `pure` equality already
  in scope.
- `with x. P` and `introduce exists* ... with ...` for explicit existentials
  (see §7).

### 5.2 Debugging a stuck proof
Whenever a proof gets stuck carefully try to debug the root issue. Often the fastest way is to work at the level of the F* file. When a proof gets stuck, try to progress the proof by adding the right assert or lemma application to the F* file. Then just rewrite the right Pulse statement in the `_ghost_stmt()` blocks in the C code.

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

### 5.3 Bridges for slprop "shape" mismatches
A common issue in proofs is the mismatch between the shape of the specification and the shape of the code. This often occurs when an invariant carries `array_pts_to_full e spec` but the body needs `array_pts_to_full v.elems spec` (or vice versa), write a ghost that does a
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

### 5.4 `[@@pulse_intro]`: which fold/unfold lemmas Pulse applies for you

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
hand — that is exactly what `$unfold-uninit(X) $&(local)` does. Forgetting
this is a common "why won't my per-field writes type-check" stall.

You can add `[@@pulse_intro]` to your *own* helper lemmas to have Pulse apply them
automatically — handy for a recurring bridge, but use sparingly: too many
auto-intro lemmas slow the matcher and can fire in unintended contexts.

### 5.5 Diagnosing a failing or slow VC

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
   Re-run with `--print_full_names --print_implicits` before adding a
   single lemma — you are usually one type-ascription away.
5. **Slow, not failing? Suspect structure first.** An opaque slprop hiding a
   `pts_to`, an existential keyed on the wrong name, or a quantified
   invariant with a bad trigger. Only after ruling those out, raise the budget —
   prefer a *target-specific* `--z3rlimit_factor` over a global bump, and
   keep it as low as still passes.
6. **Flaky (passes sometimes)?** The proof is unstable — usually an
   under-constrained quantifier or a fragile trigger. Measure with `--quake 5`
   (or `--retry`), then stabilize: name intermediate facts with `assert pure
   (...)`, pin equality types, or make a hot slprop opaque so the matcher
   can't wander. A stable proof is worth more than a fast one.
7. **Read the dump structurally.** In an Error 19/228 dump the `_pure` facts are
   your hypotheses, `_if_hyp` is the active branch condition, and the goal is the
   one thing Pulse can't close — map it back to a single invariant conjunct.

### 5.6 Iterating between a caller and a callee

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

## 6. Loops: invariants, ensures, and `break`
Adding the right loop invariants is part of both writing the specification and progressing the proof. Each loop needs to be annotated with the right loop invariant.

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
(`[@@"opaque_to_smt"]` definitions like the case-split helpers) and
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


### 6.6 Outer if-`_ensures` is mandatory when both branches return

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

## 7. Manipulating existentials (early returns + disjunctive posts)

`exists*` postconditions are auto-introduced by Pulse's matcher creating uvars
and solving them. This breaks down in a few common situations, addressed below.

### 7.1 Disjunctive post with `if-then-else` and early `return`

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
`obj_inv var_obj 1.0R var_val_pre` against the context. For the **consumer** side, eliminate such a disjunctive post in the *caller* via per-arm ghost helpers.

### 7.2 Eliminating an existential to give it a name (`with x. assert ...`)

When the context contains `exists* x. p x` and the next operation must refer to
`x` by name (pass it to a ghost helper, satisfy a pure equation):

```pulse
with w. assert (p w);   // binds w : erased _, brings p (reveal w) into context
```

This is the eliminator for `exists*`. Common uses: after unfolding a slprop with
an existential, name its witness before calling a helper; after a function call
whose post is `exists* val_post. ...`, name `val_post` to pin it. **Gotcha:**
`with x. _` (anonymous body) requires *exactly one* `exists*` in the
goal; if multiple, name each.

### 7.3 Introducing an existential with explicit witnesses

When the post has an `exists*` whose witnesses Pulse can't infer (opaque slprops,
`match`/`if` discriminants on uninferrable values, syntactic context mismatch),
provide them explicitly:

```pulse
introduce exists* x1 ... xn. p with w1 ... wn;
```

This *replaces* the matcher's uvar guess with the supplied terms; the matcher
then only discharges `p[w1/x1, ...]`.

### 7.4 Pattern combinator: name-then-introduce

`with v. assert q v; introduce exists* x. p x with v;` re-packages a context-form
existential into a goal-form existential when the two shapes differ but the
witness mapping is the identity (or a simple expression in `v`). Useful when the
context has `exists* v. q v` (e.g. from a call's post) and the goal needs
`exists* x. p x` (the enclosing function's post).

### 7.5 When to reach for explicit existentials

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
