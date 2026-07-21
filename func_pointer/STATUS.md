# Function-pointer example status

Tracks every function in `func_pointer.c` and whether it currently verifies.

- ✅ = currently verifies (`make -C func_pointer verify-one MODULE=Func_<name>`).
- ❌ *(staged)* = under `#if 0`, not emitted; does not yet verify.

`func_pointer.c` is split into an **ACTIVE** section (only the ✅ functions) and a
**STAGED** section of `#if 0` blocks (Stages 1–5 below), so the active file always
translates and verifies cleanly. Validate per module with
`make -C func_pointer verify-one MODULE=Func_<name>` (do **not** run the full
`make test`).

## Redesign: annotation families removed

> ⚠️ **The function-pointer call-site / callback annotations were removed from
> PAL entirely.** Two families no longer exist:
>
> - **`_fnptr_spec(sym)` / `_fnptr_spec(pre, post)`** — the call-site annotation
>   that named (or supplied) the validity predicate for the following indirect
>   call.
> - **`_fnptr_requires(..)` / `_fnptr_ensures(..)`** — the callback contract
>   declared on a function-pointer *parameter*.
>
> Both were deleted from `examples/pal.h`, the C++ frontend (`cpp/impl.cpp`,
> `cpp/iface.zng`), the Rust frontend (`src/clang.rs`), the IR
> (`TypeT::FnPtr { args, ret }` now carries no contract; `StmtT::FnPtrSpec` and
> `FnPtrSpecArg` are gone), the passes, and the emitter.

### What is *kept*

The "specific function pointer + calling" machinery stays: the `FnPtr` type,
address-of-function decay to `of_fn` (`emit_of_fn`), the per-function triple
`func_<g>_pre/_post/__fp` for address-taken functions (`emit_fnptr_triple`), and
the `Pulse.Lib.C.FuncPtr` library (`of_fn`, `call`, `of_fn_valid`, `weaken`,
`drop_is_valid`, `valid_cast`).
`call`/`of_fn_valid` consume/produce the `is_valid` slprop (`of_fn_valid`
is a ghost step yielding `is_valid (of_fn ..) ..`, no longer an `SMTPat` lemma).
`call`'s postcondition also **returns** `is_valid f pre post` (it is a persistent
pure fact); a proven `drop_is_valid` ghost step discards any surplus copy.

### Consequence for indirect calls

With the annotations gone there is no source for the higher-order `pre`/`post`
of a `call`. Every indirect call `fp(x)` now lowers to the value-form primitive
(the callee is read out of its ref):

```
Pulse.Lib.C.FuncPtr.call _ _ (!r) x
```

with F* **inference holes** for `pre`/`post`. F* cannot infer the higher-order
predicate on its own. **However**, when the stored pointer is a concrete
`of_fn ..` (a decayed named function), the caller can seed the missing fact at
the source level with a single ghost step just before the call:

```
_ghost_stmt(Pulse.Lib.C.FuncPtr.of_fn_valid Func_<g>.func_<g>_pre Func_<g>.func_<g>_post Func_<g>.func_<g>__fp);
```

`of_fn_valid` now yields the `is_valid (of_fn ..) ..` resource directly (it is a
ghost step, not an `SMTPat` lemma), so `call`'s `pre`/`post` holes unify
against it. This makes **concrete-store-and-call** examples verify.

What still cannot be closed this way: calls through an **abstract `func_ptr`
parameter** (callback params like `apply`/`guarded_call`) have no `of_fn` to
seed `is_valid` from — but the `is_valid` fact can instead be supplied **as a
precondition** on the parameter (see the Stage 1 section: `apply` now verifies).

> **Note (`call_ptr` removed):** PAL previously emitted a ref-form `call_ptr`
> primitive that took `r: ref (func_ptr a b)` and read it internally. That was a
> redundant wrapper around `call` (`let f = !r; call pre post f x`); it has been
> deleted from `Pulse.Lib.C.FuncPtr.fsti`, and the emitter now emits the
> value-form `call _ _ (!r) x` uniformly.

Update: the concrete-store recipe generalises much further than first expected —
**all of Stage 2** (direct stores, branch-local dispatch, and even read/copy
chains) verifies with one `of_fn_valid` ghost step per call. The remaining
blocker is genuinely the **callback-parameter** case (Stage 1), for which a
precise, validated PAL emitter fix is documented below.

## Comprehensive status table

| Function | Stage | Status | Notes |
| --- | --- | --- | --- |
| `add`, `subtract`, `neg`, `combine`, `do_nothing` | helpers | ✅ | Plain scalar helper callees. |
| `store_no_call` | active | ✅ | Stores a fnptr, never calls. |
| `use_null_init` | active | ✅ | Null init `= 0` + `fp == 0` (`is_null`). |
| `use_null_truthiness` | active | ✅ | `if (fp)` truthiness → `is_null_ptr`. |
| `use_void_cb` | active | ✅ | `do_nothing` store + call; `of_fn_valid` ghost step (emp specs). |
| `use_no_amp` | active | ✅ | `fp = add; fp(2,3)`; `of_fn_valid` ghost step. |
| `use_amp` | active | ✅ | `fp = &add; fp(3,4)`; `of_fn_valid` ghost step. |
| `use_arity1` | 2 | ✅ | `neg` (arity-1); `of_fn_valid` ghost step. |
| `use_arity3` | 2 | ✅ | `combine` (arity-3); `of_fn_valid` ghost step. |
| `use_arity3_amp` | 2 | ✅ | `&combine`; `of_fn_valid` ghost step. |
| `use_inline_declarator` | 2 | ✅ | Inline declarator spelling; `of_fn_valid`. |
| `use_typedef` | 2 | ✅ | `binop` typedef spelling; `of_fn_valid`. |
| `qualified_params` | 2 | ✅ | Qualified param types; `of_fn_valid`. |
| `func_type_decay` | 2 | ✅ | Function-type decay; `of_fn_valid`. |
| `use_cast` | 2 | ✅ | `(binop) add` cast; `of_fn_valid`. |
| `use_conditional` | 2 | ✅ | Branch-local dispatch; one `of_fn_valid` per branch. |
| `use_transitive` | 2 | ✅ | `fp2 = fp1` copy; `of_fn_valid`. |
| `use_reassign` | 2 | ✅ | Two stores/calls; one `of_fn_valid` each. |
| `use_reassign_copy` | 2 | ✅ | `fp = src` copy; `of_fn_valid`. |
| `ptr_to_fp` | 2 | ✅ | `(*pp)(2,3)` double deref; `of_fn_valid`. |
| `apply` / `use_apply_add` | 1 | ✅ | `is_valid` supplied via `_refine((_slprop) is_valid $(this) ..)` on `op`; `call` returns `is_valid`, so it threads to the ensures. `apply` keeps it; `use_apply_add` drops the surplus with a `_ghost_stmt(drop_is_valid _ _ _)` after the call. |
| `apply1` / `use_apply_neg` | 1 | ✅ | Same `_refine` recipe, arity-1 (`neg`). Caller seeds `of_fn_valid` + drops. |
| `apply_typedef` / `typedef_callback` | 1 | ✅ | Same `_refine` recipe, `binop` typedef-spelled param. |
| `apply_weaker` / `weaken_callback` | 1 | ✅ | Callback declares a WEAKER post; the `Apply_weaker_spec` `_include_pulse` module defines the weak post + a `weaken` coercion ghost; `weaken_callback` seeds `subtract`'s validity, `weaken`s it, then calls + drops. Annotation-level only. |
| `guarded_call` | 1 | ✅ | `_nullable` callback; `_refine` wraps `is_valid` in `unless_null`. The `if (fp)` branch `elim_unless_null_nonnull`s to `is_valid` for the call and `intro_unless_null_nonnull`s it back for the ensures. **Needed a library addition:** a `has_is_null (func_ptr a b)` instance in `Pulse.Lib.C.FuncPtr` (analogous to the existing `ref`/`array` instances). |
| `reassign_join_call`, `reassign_join` | 3 | ✅ | Join-family; `fp` bound to different targets per branch, called AFTER the merge. Verified **annotations-only** via an `_ensures` on the `if` that carries the raw join existential inline: `exists* v. pts_to $&(fp) v ** is_valid v (rj_pre g) (rj_post g)`, which hides the branch-differing pointer value behind an existential keyed on the common guard `g = int32_to_bool g_use_sub` (a `ghost_read` before the `if`). Each arm derives its per-branch validity with a single `FuncPtr.weaken` (after `of_fn_valid` for the named fn) landing directly on `(rj_pre g)(rj_post g)`; Pulse auto-introduces the existential at the branch boundary and unfolds it after the merge for the post-join `call`. Both `rj_pre` and `rj_post` are `unfold`, so the call precondition reduces and the value postconditions discharge automatically — no `key_sub`/`key_add`, `intro_joined`/`elim_joined`, or `finish` helpers are needed. |
| `assign_from_agg` | 3 | ✅ | Read a func-ptr out of a stack array into a local, then call it. Same recipe as `use_array_slot` (below): bind the stored value to a local before `array_write` (so `array_spec_initd` stays provable at the read), then `valid_cast` the read-back value onto the `of_fn` validity before the call. |
| `use_struct_field` | 4 | ✅ | Fnptr in a struct field: `o.op = add; o.op(2,3)`. Local `struct ops o;` is `pts_to_uninit`, so a `_ghost_stmt($unfold-uninit(struct ops) $&(o))` exposes the per-field cell before the store (PAL does not auto-emit the unfold for a locally-declared uninitialised struct). Then the usual `of_fn_valid` before the call + `drop_is_valid` after. |
| `union_field` | 4 | ✅ | Fnptr in a union field: `u.op = add; u.op(2,3)`. Works with just the `of_fn_valid`/`drop_is_valid` pair — the union arm write/activation is emitted automatically (no `$activate`/`$unfold-uninit` needed for a scalar-typed arm). |
| `malloc_fp` | 4 | ✅ | Fnptr in a heap cell: `*pp = add; (*pp)(2,3); free(pp)`. The prior "Error 228 at the indirect call" note was stale — the recipe threads straight through the heap deref: `of_fn_valid` before `int32_t r = (*pp)(2,3)`, `drop_is_valid` right after the binding, then `free`. |
| `use_array_slot` | 4 | ✅ | Fnptr stored in a stack-local fixed-array slot, read back, and called. Two obstacles beyond the (now-fixed) `array_read` lowering: (1) `array_write` inlining the `of_fn ..` higher-order term blocks the SMT E-match for `array_spec_initd` at the read — fixed by binding the stored value to a local (`tmp`) so the spec updates against an opaque term; (2) `array_read` yields a value only *provably* (not syntactically) equal to the stored `of_fn ..`, so the `is_valid (of_fn ..) ..` from `of_fn_valid` doesn't match the read value's `is_valid` key. **Needed a library addition:** `valid_cast` in `Pulse.Lib.C.FuncPtr` (re-keys a validity fact across a provable pointer equality; pre/post inferred from context). Recipe: bind `tmp`, `tbl[0]=tmp`, read into `f`, `of_fn_valid`, `valid_cast _ $(f)`, call, `drop_is_valid`. |
| `multilayer` | 4 | ✅ | Array-elem → struct-field → call. Combines the `use_array_slot` recipe (bind `tmp`; `valid_cast` the array-read value) with the `use_struct_field` recipe (`$unfold-uninit(struct ops) $&(o)` before writing `o.op`). The `valid_cast` re-keys onto the value read out of the array (`$(slot)`), which is also what the struct field then holds. |
| `inc`, `ptr_arg_cb` | 4 | ✅ | **Ownership-pointer argument through an indirect call.** `inc(int32_t *p) _requires(*p<100) _ensures(*p==_old(*p)+1)` has a *relational* spec; `ptr_arg_cb` does `void (*f)(int32_t*) = inc; f(p)`. The synthesized fnptr triple (`func_inc_pre`/`func_inc_post`/`func_inc__fp`) threads the pointer's **initial pointee value** through the FuncPtr domain `a` (now `ref ty_int32_t & ty_int32_t`), so the non-relational contract (`pre: a->slprop`, `post: a->b->slprop`) can still name `_old(*p)`. In the emitted spec (`src/pass/emit.rs`: `fnptr_domain_with_old` + `emit_fnptr_spec_core`), the pre pins `pts_to p #1.0R var_p_old`, the post existentially binds the current value `var_p_cur`, `*p` resolves to `var_p_cur` (post) / `var_p_old` (pre), and `_old(*p)` to `var_p_old` — replacing the ill-typed `!var_p` stateful read inside a bare `slprop`. The wrapper calls `func_inc (fst x_fp)` (projection passed directly, not `let`-bound, so the prover matches the `pts_to` precondition). At the call site the ref and its current pointee are bound in a prelude (`let __pal_fpref = !var_p; let __pal_fpold = !__pal_fpref;`) and passed as the pure tuple `(__pal_fpref, __pal_fpold)` — a bare `!r` read is stateful and an inference hole for the old value elaborates at a ghost effect. Recipe: `of_fn_valid` before the call, `drop_is_valid` after. |
| `designated_vtable` | 5 | ✅ | Designated-init `struct ops_c o = { .op = add }; o.op(2,3)`. Straight concrete-store recipe: `of_fn_valid` for `add` before the call, `drop_is_valid` after. The aggregate initialiser already establishes the field cell, so (unlike `use_struct_field`) no `$unfold-uninit` is needed. |
| `dispatch` / `use_dispatch` | 5 | ✅ | Cross-function dispatch through a struct field, threaded via a **`_refine_value` field contract**. A `_type(ops_c_val, Struct_ops_c.struct_ops_c)` + `_refine_value(ops_c_val vo, _inline_pulse(Dispatch_spec.ops_c_valid $(this) $(vo)))` on `typedef struct ops_c *ops_c_ptr` gives the pointer type an ownership predicate `ops_c_valid this vo = pts_to this vo ** is_valid vo.op add_pre add_post`. `ops_c_valid` is declared **`unfold`** (so the field `pts_to` is exposed for the struct's `pulse_intro` unfold/fold at the `o->op` read). `dispatch(ops_c_ptr o,..)` then calls `o->op(a,b)` and proves `return==a+b` straight from the field's carried `is_valid`. `use_dispatch` declares `struct ops_c o` (needs `$unfold-uninit(struct ops_c)` before `o.op = add`), seeds `of_fn_valid` for `add` so the refinement holds when passing `&o`, and drops the surplus `is_valid` (returned inside `dispatch`'s ensures pred) with `drop_is_valid` after the call. The `struct ops_c *` parameter is spelled via the `ops_c_ptr` typedef (semantically identical, same pattern as `apply_typedef`/`recursive_struct`'s `list`). |
| `return_fp` (with `select_op`) | 5 | ✅ | Fnptr **returned** from `select_op` and called by `return_fp`. `select_op` carries a **guard-keyed return-validity** `_ensures(_inline_pulse(is_valid return_1 (Reassign_join_spec.rj_pre (int32_to_bool var_use_sub)) (rj_post ..)))` (reuses the `Reassign_join_spec` module); a `ghost_read` of `use_sub` gives the pure guard, and each arm seeds `of_fn_valid` + `weaken`s the concrete pointer onto the guard-keyed spec (exactly the `reassign_join` recipe). `return_fp` calls `select_op(0)` (→ `add` spec), calls through the returned pointer to get `return==5`, and `drop_is_valid`s the surplus. **Note:** `select_op` is written as an explicit `if`/`else` (semantically identical to a `return use_sub ? subtract : add;` ternary) so each arm has a C-source site for its per-arm `of_fn_valid`+`weaken` ghosts. The verbatim ternary-return form emits synthesized branch returns with no per-arm site to seed the validity ghosts, so that form would need an emitter feature to attach per-arm ghosts to ternary/return arms. |
| `array_runtime_idx` | 5 | ✅ | Runtime-indexed fnptr array `tbl[i]` with `_requires(i==0||i==1)`. Same recipe as `use_array_slot` (bind `tmp`, both slots `= tmp`, read `tbl[i]` into `f`, `of_fn_valid`, `valid_cast _ $(f)`, call, `drop_is_valid`). Because both slots hold `add` and `i∈{0,1}`, the runtime-index read is provably `add`, so `array_spec_initd`/`array_spec_mask` at `i` and the `valid_cast` value equality both discharge. |
| `rec_via_ptr` | 5 | ❌ | **Deferred (emitter mutual-recursion gap).** Taking the address of the function under definition (`self = rec_via_ptr`) decays to `of_fn .. func_rec_via_ptr__fp` inside `func_rec_via_ptr`'s body, referencing the lifted triple `func_rec_via_ptr__fp`, whose body calls back into `func_rec_via_ptr`. PAL emits the two as **separate** top-level `fn`s (not a `fn rec .. and ..` group) with `func_rec_via_ptr` first, so its `of_fn .. func_rec_via_ptr__fp` is a forward reference to a later-defined name → F* Error 72 "Identifier not found: func_rec_via_ptr__fp". (Independently, self-module-qualified annotations like `Func_rec_via_ptr.func_rec_via_ptr_pre` self-import the interface → Error 47 duplicate top-level names; using unqualified names avoids that but not the forward reference.) Confirmed by hand: emitting the two as a mutually-recursive group is the fix, which is a `src/**` emitter change. |

## Active examples (all verify ✅)

The active section of `func_pointer.c` contains every ✅ function above: the
helpers, the original active set, all of **Stage 2** (now un-fenced), the Stage 3
join family, the Stage 4 struct/union/heap cases, and the Stage 5 verifiers
(`designated_vtable`, `select_op`+`return_fp`, `dispatch`+`use_dispatch`). Each
Stage 2 call site carries one `of_fn_valid` ghost step immediately before the
call (per branch, for `use_conditional`), and one
`_ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _)` immediately after it to
discard the surplus `is_valid` that `call` now returns.

## Stage 1 — Callback parameters: ALL VERIFIED via `_refine`

**All of Stage 1 now verifies.** `apply`/`apply1`/`apply_typedef` use the plain
`_refine` recipe; `apply_weaker` adds an annotation-level `weaken` coercion;
`guarded_call` adds `unless_null` elim/intro plus one small library instance.
`apply`/`use_apply_add` were the first, after a library change that makes validity
a persistent fact `call` hands back (the drop of any surplus is a source
annotation, not an emitter change).

**What works:** annotate the callback parameter with a `_refine((_slprop)
is_valid $(this) ..)`, which lands `is_valid` in **both** the generated
`requires` and `ensures`:

```c
int32_t apply(int32_t (*op)(int32_t, int32_t)
                  _refine((_slprop) _inline_pulse(
                      Pulse.Lib.C.FuncPtr.is_valid $(this)
                          Func_add.func_add_pre Func_add.func_add_post)),
              int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{ return op(a, b); }
```

`apply1` (arity-1, `neg`) and `apply_typedef` (`binop` typedef spelling) are
identical modulo the spec names / parameter type. Each *caller* seeds
`of_fn_valid` before the call and drops the surplus after.

**The PAL change that makes `_refine` verify.** Previously `call`'s postcondition
returned only `post x r`; it **consumed** `is_valid` and handed nothing back, so
requiring `is_valid` to *survive* to the `ensures` (as `_refine` does) forced
Pulse to frame the requires' fact through untouched and solve the `_ _` pre/post
holes from the continuation → failure. Now `call`'s postcondition also **returns**
`is_valid f pre post` (validity is a pure, persistent fact — calling through a
pointer does not invalidate it), so the fact threads across the call and
discharges the `_refine` ensures.

**Consequence + fix (surplus `is_valid`).** Because every `call` now returns
`is_valid`, callers that don't carry it in their own `ensures` (every Stage-2
example, and every caller of a contracted-callback function like `apply`) would
hold a *leftover* validity resource. The library adds a **proven** ghost step
`drop_is_valid` (`is_valid` unfolds to `pure`, so it drops back to `emp`). PAL
does **not** insert it automatically; instead each such call site carries a
source annotation `_ghost_stmt(Pulse.Lib.C.FuncPtr.drop_is_valid _ _ _)` after the
call:

- after an indirect `call` on a concrete `of_fn` local (every Stage-2 example),
  placed right after the `return fp(..)` (or after the binding statement for a
  mid-function call), and
- after a call to a function that re-exports `is_valid` in its `ensures` (like
  `apply` in `use_apply_add`).

The `_ _ _` holes resolve against the unique leftover by the `[@@@mkey]` on `f`,
and PAL's return-then-ghost rewrite runs the drop live before the `return`.
`apply` itself carries **no** drop — its `_refine` exports `is_valid` in the
`ensures`, so the returned fact threads through to satisfy it.

**`apply_weaker` / `weaken_callback` (weaker post via `weaken`).** The callback
declares a post (`return < a`) weaker than what `subtract` provides
(`return == a - b`). An `_include_pulse` module `Apply_weaker_spec` defines the
weak post `aw_post` plus a `weaken_sub_to_aw` ghost that calls the library
`weaken` (with an identity pre-coercion and a post-coercion proving
`return == a - b ==> return < a` under the shared precondition). `apply_weaker`'s
`_refine` uses `subtract`'s pre with `aw_post`; `weaken_callback` seeds
`subtract`'s validity, applies `weaken_sub_to_aw`, calls, and drops. All of this
is annotation-level (no PAL/library change).

**`guarded_call` (`_nullable`) — needed one small library instance.** A
`_nullable _refine((_slprop) is_valid $(this) ..)` parameter emits its refinement
wrapped in `unless_null var_fp (is_valid ..)`. Two things are required:

1. `unless_null` needs a `has_is_null (func_ptr a b)` typeclass instance. There
   was none (only `ref`/`array` had one), and a user instance supplied via
   `_include_pulse` cannot be brought into the generated module's scope — so this
   is a genuine **library gap**. Fix (kept): add to `Pulse.Lib.C.FuncPtr.fsti`
   ```fstar
   instance has_is_null_func_ptr (a b: Type0)
     : Pulse.Lib.C.Nullable.has_is_null (func_ptr a b) = { test_null = (fun f -> is_null f) }
   ```
2. In the `if (fp)` (non-null) branch, source annotations
   `_ghost_stmt(Pulse.Lib.C.Nullable.elim_unless_null_nonnull $(fp) (is_valid ..))`
   (before the call, to extract `is_valid` from `unless_null`) and
   `_ghost_stmt(.. intro_unless_null_nonnull $(fp) (is_valid ..))` (after, to
   rebuild `unless_null` for the ensures). The `p` argument must be given
   explicitly — inference (`_`) fails on the `intro`. No drop here (the returned
   `is_valid` is reused to re-establish `unless_null`).

## Stages 3–5

- **Stage 3 — Join family:** `reassign_join_call`, `reassign_join` **✅ verify**
  (annotations-only). `fp` is bound to different targets per branch and called
  after the merge; an `_ensures` on the `if` carries the raw join existential
  inline — `exists* v. pts_to $&(fp) v ** is_valid v (rj_pre g) (rj_post g)` keyed
  on the common guard `g` — and each arm lands its per-branch validity with one
  `FuncPtr.weaken` (after `of_fn_valid`). Both `rj_pre`/`rj_post` are `unfold`, so
  the post-merge `call` and value postconditions discharge automatically. There is
  no `rj_joined` predicate and no `intro_joined`/`elim_joined`/`finish`/`key_sub`/
  `key_add` helpers — the existential is carried inline, not behind a named wrapper.
  `assign_from_agg` **✅ verifies** — a func-ptr read out of a stack array into a
  local, then called, via the `use_array_slot` recipe (bind stored value; `valid_cast`).
- **Stage 4 — Fnptr as data:** `use_struct_field`, `union_field`, `malloc_fp`,
  and `ptr_arg_cb` (with `inc`) **✅ verify** (struct/union/heap cell + the
  `of_fn_valid`/`drop_is_valid` recipe; `use_struct_field` also needs
  `$unfold-uninit(struct ops)`; `ptr_arg_cb` threads the pointer's initial
  pointee value through the fnptr domain so the callee's relational `_old(*p)`
  spec composes — see the table row). `use_array_slot` and `multilayer` now
  **✅ verify**: after the stack-local fixed-array read fix (`emit.rs ExprT::Index`
  emits `array_read`), two obstacles remained — `array_write` inlining the `of_fn`
  higher-order term blocks the `array_spec_initd` SMT E-match (fixed by binding the
  stored value to a local), and the array-read value is only *provably* equal to
  the stored `of_fn` (fixed by a new `valid_cast` library ghost that re-keys the
  `is_valid` fact across a provable pointer equality). See the table rows.
- **Stage 5 — Advanced / edge:** `designated_vtable`, `dispatch`/`use_dispatch`,
  and `return_fp` (with `select_op`) **✅ verify** (annotations-only).
  `designated_vtable` is the plain concrete-store recipe on a designated-initialised
  local. `dispatch`/`use_dispatch` thread `is_valid` across a by-ref struct pass via a
  **`_refine_value` field contract** (`ops_c_valid this vo = pts_to this vo **
  is_valid vo.op add_pre add_post`, declared `unfold`); the callee reads/calls
  `o->op` straight from the carried validity, and the caller seeds `of_fn_valid` +
  `$unfold-uninit` and drops the surplus. `return_fp` uses a **guard-keyed
  return-validity `_ensures`** on `select_op` (reusing `Reassign_join_spec.rj_pre/
  rj_post` + `weaken` per arm); `select_op` is written as an explicit `if`/`else`
  (semantics-identical to a `return use_sub ? subtract : add;` ternary) because the
  ternary-return form has no per-arm C-source site to seed the validity ghosts.
  `array_runtime_idx` **✅ verifies**
  (runtime-indexed `tbl[i]`, `i∈{0,1}`, both slots `add` — same `use_array_slot`
  recipe; the runtime-index read is provably `add`), and
  `rec_via_ptr` is **deferred** on an emitter mutual-recursion gap: the self-address
  decay `self = rec_via_ptr` makes `func_rec_via_ptr` forward-reference its lifted
  `func_rec_via_ptr__fp` triple, which PAL emits as a separate (non-`rec`-grouped)
  top-level `fn` → F* Error 72; the fix is to emit the function and its address-taken
  triple as one mutually-recursive group (`src/**`).
