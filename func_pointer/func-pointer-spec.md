# Function pointers in PAL

The goal is to support **function pointers** in the C → Pulse transpiler. The
approach has two parts:

1. An axiomatized Pulse library, `pulse/Pulse.Lib.C.FuncPtr.fsti`, that gives a
   *uniform* runtime representation of a function pointer — a value that can be
   stored, passed, compared against null, and called without the caller knowing
   the concrete target it currently holds.
2. Transpiler support (in `src/`) that lowers C function-pointer declarations,
   stores, and indirect calls onto that library.

Test cases live in `func_pointer/func_pointer.c`; each C function becomes its own
F* module `Func_<name>` (see `checking-a-single-function.md`).

## Storing a function into a pointer: `&` is optional

C allows a function to decay to a pointer with or without `&`. Both spellings
must be handled and mean the same thing:

```c
int add(int a, int b) { return a + b; }

int (*fp1)(int, int) = add;    // no & needed
int (*fp2)(int, int) = &add;   // explicit address-of
```

## The Pulse specification

The core of `Pulse.Lib.C.FuncPtr.fsti`:

- `func_ptr (a b: Type0) : Type0` — an abstract function-pointer type. `a` is the
  (tupled) argument type, `b` the return type. It is inhabited by `null`, so a
  `func_ptr` can be stored in refs, struct fields, arrays and globals.
- `valid (f: func_ptr a b) (pre: a -> slprop) (post: a -> b -> slprop) : prop` —
  the pointer `f` meets the spec `(pre, post)`. A *pure* proposition, so it is
  threaded as a `squash` fact without touching the heap. Keeping `valid` off the
  `func_ptr` type is what lets pointers stay spec-agnostic (storable, nullable,
  zero-initialisable).
- `is_valid (f: func_ptr a b) (pre: a -> slprop) (post: a -> b -> slprop) : slprop`
  — the **slprop wrapper** of `valid`, defined as `pure (valid f pre post)`. This
  is the *core* validity form used in the `stt` contracts: `call` and `weaken`
  consume (and, for `weaken`, produce) `is_valid` so that validity
  travels as a heap-resource fact in the Pulse proof context, rather than as a
  bare `squash` argument. `valid` remains the underlying pure `prop`; `is_valid`
  is how it enters a resource context. (`[@@@mkey]` on `f` keys the resource on
  the pointer value.)
- `null (a b: Type0) : func_ptr a b` — the null pointer. `null_invalid` states it
  is never `valid` at any spec.
- `of_fn pre post f : func_ptr a b` — reflect a concrete Pulse function `f` (with
  a statically-known spec) as a pointer. `of_fn_valid pre post f` is a ghost step
  producing `is_valid (of_fn pre post f) pre post` directly, so a caller holding a
  concrete `of_fn ..` can introduce its `is_valid` resource with a single ghost
  step (no separate `fold` of a pure `valid` fact).
- `call pre post (f: func_ptr a b) (x: a)
  : stt b (is_valid f pre post ** pre x) (fun r -> post x r)` — the single,
  uniform indirect-call primitive. Validity is consumed as the `is_valid` slprop
  (no longer a `squash` proof argument). The emitter evaluates the callee to a
  `func_ptr` value (an `!r` read for a mutable local) and hands it to `call`;
  there is no separate ref-form primitive. `pre`/`post` are explicit because SMT
  cannot solve for the higher-order spec metavariables.
- `weaken` — transfer validity from `(pre, post)` to a weaker `(pre', post')`
  given ghost coercions between the pre/postconditions; consumes
  `is_valid f pre post` and produces `is_valid f pre' post'`.
- `is_null` / `fp_eq` — decidable null test and pointer equality, so C
  `if (fp)`, `fp == NULL`, and `fp1 == fp2` translate.

### Merging pointers across a control-flow join

When a pointer is assigned *different* concrete targets in the two arms of a
conditional and called after the join, the two arms must produce the *same*
`slprop` so it merges cleanly. Two proved (non-axiom) lemmas support this by
splitting on both the pointer and the spec:

- `valid_if cond f1 f2 pre1 pre2 post1 post2` — from
  `if cond then valid f1 pre1 post1 else valid f2 pre2 post2`, derive
  `valid (if cond then f1 else f2) (if cond then pre1 else pre2)
        (if cond then post1 else post2)`.
- `call_if` — the analogue for `call` with arbitrary (heapful) `slprop`
  contracts: given the merged validity `valid_if` produces, call the merged
  pointer once, with branched pre/post `if cond then p1 x else p2 x` /
  `if cond then q1 x r else q2 x r`.

### Function-pointer arrays

A `func_ptr` value alone is not callable — calling needs the separate `valid`
fact. To recover callability of an array element at a *runtime* index (where no
single static target exists), the library provides an array-level invariant:
every initialised slot is valid at one common spec.

- `array_all_valid s pre post : prop` — every initialised slot of the spec
  sequence `s` is valid at `(pre, post)`.
- `array_all_valid_idx s pre post i` — an in-bounds initialised slot is callable
  at the common spec.
- `array_all_valid_upd s pre post n x` — storing a valid pointer preserves the
  invariant.

## Feature roadmap (C surface to support)

The transpiler should eventually support every way C programs use function
pointers. Grouped by category, with the representative test-case names from
`func_pointer.c`:

### Storing
- Decay with / without `&`: `fp = add;`, `fp = &add;` — `use_no_amp`, `use_amp`
- Transitive copy from another pointer, including chains — `use_transitive`
- Straight-line reassignment (same pointer, different targets at different
  points) — `use_reassign`, `use_reassign_copy`
- Reassignment across a control-flow join, call after the join — `reassign_join`
- Assignment from an aggregate that yields a pointer — `assign_from_agg`

### Calling
- All fixed arities incl. zero-arg / `void` return — `use_arity1`, `use_arity3`,
  `use_arity3_amp`, `use_void_cb`
- Return value used, discarded, or in `return fp(...)`
- Pointer / ownership arguments flowing through the call (`pts_to` contract
  inherited) — `ptr_arg_cb`
- Calls where the concrete callee is not statically known — `reassign_join`,
  `array_runtime_idx`, `dispatch`

### Type spellings
- Inline declarator types `int (*fp)(int,int)` — `use_inline_declarator`
- `typedef`'d function-pointer types — `use_typedef`
- Qualified / `const` parameters in the signature — `qualified_params`
- Function types (not pointers) that decay — `func_type_decay`
- Pointer-to-function-pointer `int (**pp)(int,int)` — `ptr_to_fp`

### As data
- As a **callback parameter**: `apply(int (*op)(int,int), int a, int b)` — the
  single biggest real-world case — `apply`/`use_apply_add`, `apply1`/`use_apply_neg`
- Branch-local conditional dispatch — `use_conditional`
- In a **struct** field — `use_struct_field`
- In an **array** element — `use_array_slot`
- In a **union** field — `union_field`
- Via a **dynamically allocated** pointer — `malloc_fp`
- Passing a function with a *stronger* contract to a callback (needs `weaken`) —
  `weaken_callback`
- Typedef'd callback-parameter spellings — `typedef_callback`
- As a **return value** — `return_fp`
- Cross-function dispatch through a **struct** field (vtable / OO) —
  `dispatch`/`use_dispatch`
- Runtime-varying **array** dispatch (non-constant index) — `array_runtime_idx`

### Null and comparison
- Null init `= NULL;` / `= 0;` — `use_null_init`
- Null checks used as a boolean (`if (fp)`, `fp == NULL`, `fp != NULL`) —
  `use_null_truthiness`
- Guarded call where the pointer carries a contract — `guarded_call`

### Advanced / edge cases
- Casting between compatible function-pointer types — `use_cast`
- Threading a pointer through several layers within one function — `multilayer`
- Indirect recursion through a function pointer — `rec_via_ptr`
- Designated-initializer vtables / dispatch tables — `designated_vtable`
- Multi-layer passing across function boundaries
