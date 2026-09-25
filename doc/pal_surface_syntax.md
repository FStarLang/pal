# PAL surface syntax

PAL programs are C files annotated with macros declared in `pal.h`. Under `-DC2PULSE` each macro expands to a Clang `__attribute__((annotate("pal-...")))`; without it the macros vanish and the file compiles as ordinary C.
These macros are used to give specifications to types and functions.
This document explains how to write these specifications using PAL.


In the following, we differentiate between two kinds of annotations:
1. `_requires` / `_ensures` / `_invariant` / `_refine` are used to add specifications for functions and types as well as loop invariants.
2. When these annotations are not enough for specifying some function or for progressing the proof then PAL provides annotations such as `_ghost_arg`, `_ghost_stmt`, `_assert`, `_inline_pulse`, `_include_pulse` that reach the Pulse layer directly when the surface syntax isn't enough.

<!-- 3. **Default ownership** — for every non-`_plain` parameter PAL implicitly threads an in-memory resource (e.g. `pts_to`, `array_pts_to_full`) into both `requires` and `ensures`.
4. **User contracts** — `_requires` / `_ensures` / `_invariant` / `_refine*` add pure or spatial predicates over those resources.
5. **Ghost glue** — `_ghost_arg`, `_ghost_stmt`, `_assert`, `_inline_pulse`, `_include_pulse` reach the Pulse layer directly when the surface syntax isn't enough.

To suppress the default ownership for one parameter, prefix it with `_plain`. -->

## Variadic calls with an ignored tail

PAL supports direct calls to variadic functions whose bodies do not access
the variadic arguments. The generated function and its calls contain only
the fixed parameters; extra arguments do not transfer ownership to the
callee.

For this initial support, ignored arguments must be scalar literals,
non-volatile/non-atomic scalar or pointer local/parameter values, or addresses
of ordinary local variables or parameters. Parentheses and implicit value
conversions (including default promotions) are allowed. Computations,
dereferences, member/subscript reads, side effects, and other unsupported
extra expressions are rejected rather than silently skipping their evaluation.
Indirect variadic calls and variadic argument extraction are not supported.

For example, `read_first(int *first, ...)` may return `*first`, and a caller
may use `read_first(&a, &b, &c)`. Only `&a` is passed in the generated Pulse
call. See `test/variadic_call/variadic_call.c`.

## Syntax for specifications

### Annotating function arguments
For every function, PAL by default adds pre and post conditions for every argument: the precondition requires ownership of the argument and the post returns it. The default fits most cases; the annotations below override it when a parameter is consumed, returned-only, or treated as an array.

| C syntax                  | implicit resource in `requires` / `ensures`         |
|---------------------------|-----------------------------------------------------|
| `_plain T x`              | suppresses the auto-generated spec for this parameter; user supplies its own pre / post |
| `_consumes T *x`          | `pts_to` in `requires` only — not returned          |
| `_out T *x`               | `pts_to_uninit` in `requires`, `pts_to` in `ensures`|
| `_array T *x` / `T x[]`   | `array_pts_to_full var_x 1.0R val_x_0`              |
| `_arrayptr T *x`          | `arrayptr_pts_to var_x parent`                      |

Beyond ownership, the user typically also wants to constrain values. PAL provides the following annotations for adding extra contract clauses:

- `_requires(p)` / `_ensures(p)` — extra pre / post predicates on a function.
- `_preserves(p)` = `_requires(p) _ensures(p)`.
- `_preserves_value(x)` = `_ensures(x == _old(x))`.
- `_invariant(p)` / `_ensures(p)` on a loop — see below.
- `_decreases(p)` — termination measure on a `_rec` function (required there; not a loop annotation).
- `_assert(p)` — verification assertion inside a function body.

Inside any of these predicates the following spec-only constructs are available:

- `_old(x)` — value of `x` at function entry.
- `_live(x)` — slprop asserting `x`'s resource is currently owned.
- `x._length` — runtime length of an array.
- `_specint` — arbitrary-precision integer (ghost arithmetic).
- `_slprop` — type cast used in `_refine` to declare a separation-logic predicate.
- `$(...)` — antiquotation: splice a C-level entity into an `_inline_pulse` body (see the Antiquotation section under Pulse interop).

### Loop invariants

Loops (`while` / `for` / `do-while`) carry their own contracts via `_invariant` and `_ensures`. Each occurrence of `_invariant(p)` becomes one Pulse `invariant` clause; stacking is the standard way to combine a separation-logic invariant with one or more pure invariants:

```c
for (uint32_t ctr = 0; ctr < x; ctr = ctr + 1)
  _invariant(_live(ctr) && _live(acc))
  _invariant(ctr <= x && acc == ctr * y)
{
  acc = acc + y;
}
```

lowers to:

```
while (...)
  invariant ((live var_ctr) ** (live var_acc))
  invariant (with_pure ((!var_ctr `UInt32.lte` !var_x) && (!var_acc = !var_ctr `UInt32.mul` !var_y)))
{ ... }
```

Inside `_invariant`:

- Parameters and locals are in scope by name; there is no `this`.
- `_live(x)` asserts the points-to permission for a C local `x` (e.g. `ctr` and `acc` above) — it must appear in the invariant for every local the loop body reads or writes.
- Read a local's current value with `*x` or `!x`; both are accepted.

`_ensures(p)` may also be attached to a loop. It records the condition that must hold when the loop exits via `break`: write one `_ensures` per `break` site (each becomes a separate disjunct of the loop's post-condition). Each `_ensures` lowers to one Pulse `ensures` clause on the `while`. Example from `test/break_continue/break_continue.c`:

```c
while (i < n)
  _invariant(_live(i))
  _invariant(i <= n)
  _ensures(i <= n)            // discharged at the single `break`
{
  if (i == limit) { break; }
  i = i + 1;
}
```

lowers to:

```
while (...)
  invariant (live var_i)
  invariant (with_pure ((!var_i) `UInt32.lte` (!var_n)))
  ensures ((!var_i) `UInt32.lte` (!var_n))
{ ... }
```

A loop with two `break` sites would carry two `_ensures` clauses, one for each.

For `do { ... } while (cond)`, PAL desugars to `while (first || cond)` with a fresh boolean flag. Use `_do_while_first(name)` to name that flag explicitly when the invariant needs to refer to it (see `test/do_while/do_while.c`).

### Refinements for data types

As explained in `structs.md`, PAL auto-generates predicates for compound types. These can be further enriched with user-supplied predicates carried by the type itself:

| annotation                  | when the predicate must hold              |
|-----------------------------|-------------------------------------------|
| `_refine(p)`                | when the value is initialized             |
| `_refine_always(p)`         | always, even when uninitialised           |
| `_refine_uninit(p)`         | only when uninitialised                   |
| `_refine_value(bind, pred)` | as `_refine`, but binding name is `bind`  |

A refinement does *not* change the runtime representation. It is attached to the **type** at every site where the type appears (parameter, struct field, return value, …) and is materialised as an extra pure conjunct in any slprop emitted for a value of that type — e.g. in the implicit `pts_to` of a function parameter. Whether that conjunct ends up *inside* the type's auto-generated `__pred` or *alongside* it at each use site depends on where the refinement is written: a field-level refinement is folded into the struct's `__pred` (see below), whereas a refinement on a struct or typedef declaration itself is kept separate and re-attached at every use site, leaving `struct_S__pred` unchanged (see below). Folding a record/typedef-level refinement directly into `struct_S__pred` instead is potential future work, not current behavior.

**On a typedef** — the refinement fires for every use of the typedef.

```c
_refine(this._length == 32) typedef _array uint8_t *uds_array;

void f(uds_array a) { ... }
// requires: array_pts_to_full var_a 1.0R val_a_0 ** pure (length_of var_a == 32)
```

`_refine_always` on a typedef is the form to use when the type also appears in `_out` position, since the refinement then has to hold in the uninit precondition too.

**On a struct declaration** — `this` is the whole record; reach into fields with `this.<field>`. PAL parses the declaration's type attributes once, stores the attributed self type on the struct definition, and reuses it whenever `struct S` is referenced. Thus the refinement fires at every use while `struct_S__pred` itself remains unchanged; repeated mentions do not reparse the annotation. The annotation must be written *after* the `struct` keyword, otherwise clang ignores it.

```c
struct _refine(0 < this.x) simpler { int x; };

void f(struct simpler s) { ... }
// requires: struct_simpler__pred var_s 1.0R val_s_0
//        ** with_pure (0 < var_s.struct_simpler__x)
```

`_plain` composes here too, which is how a record-level `_refine(_inline_pulse ...)` can replace the default ownership predicate outright — see [`test/refine_struct/refine_struct.c`](../test/refine_struct/refine_struct.c). Record-level annotations on `union` declarations are not supported yet; use a typedef for those.

**On a field type** — the refinement applies to that field's value; inside the predicate `this` is the field, not the surrounding record. The refinement is added to the per-field clause of the struct's pred when emitted.

```c
struct s {
    _refine(0 < this) int x;
};
```

The record-level and field-level forms differ in scope: record-level binds `this` to the whole struct value (so the predicate may relate several fields), while field-level binds `this` to that one field and is folded into the field's clause of the struct's pred.

### Ghost code

PAL exposes two ghost constructs for proof assistance that have no runtime effect:

- `_ghost_arg(T name)` — extra parameter erased at runtime; usable only in specs and ghost statements.
- `_ghost_stmt(expr)` — Pulse statement executed only during verification (e.g. applying a lemma).

Ghost arguments do not change C function-pointer signatures. Generated
wrappers forward them through erased witnesses. If inference cannot determine
a call's ghost arguments, supply a witness with a ghost statement; the callee's
precondition must still hold. Taking a function's address requires no witness.
See `test/func_pointer/func_pointer.c` for examples.

## Pulse interop

- `_inline_pulse(expr)` — embed a Pulse expression in a spec position.
- `_include_pulse(Mod, snippet)` — drop a verbatim Pulse block (definitions, lemmas, helpers) into a module `Mod`.
- `_let(sig, body)` / `_let_rec(sig, body)` / `_letimpure(sig, body)` — Pulse-level top-level bindings.
- `_type(name, body)` — Pulse-level type definition.

### Antiquotation

Inside an `_inline_pulse(...)` body — and the spec macros built on it — text is emitted to Pulse **verbatim**; antiquotations are the `$`-prefixed forms PAL rewrites into C-level entities (`pts_to`, `exists*`, `**`, `pure`, module names, etc. pass through untouched).

| form | emits |
|------|-------|
| `$(expr)`                                 | the **value** (rvalue) of a C expression — variable, `*p`, `x.f`, `_container_of(...)`, `this`, `return` |
| `$&(expr)`                                | the **reference cell** (`ref a`), not dereferenced — e.g. for a `pts_to` over a local |
| `$type(c-type)`                           | the F* type for a C type (`$type(int *)`, `$type(struct s)`) |
| `$field(Type::f)`                         | a struct field accessor, or a union field constructor |
| `` $`ident ``                             | `'ident` (an F* implicit / ticked name); in an `exists*` position, a fresh existential of inferred type. Infix: `` pfx$`sfx `` → `pfx'sfx` |
| `$declare(Type id)`                       | nothing — binds `id : Type` in the annotation's scope so a later `$(id)` resolves |
| `$unfold(T)` / `$fold(T)`                 | the generated raw unfold / fold lemma for `T`'s ownership predicate |
| `$unfold-uninit(T)` / `$fold-uninit(T)`   | the uninit-variant lemma (struct only; **not** auto-applied) |
| `$unfold(U::f)` / `$fold(U::f)`           | the unfold / fold lemma for union field `f` |

Notes:

- **Context sensitivity.** A parameter `p` is rebound as `let mut var_p = var_p;`, so `$(p)` is the parameter *value*: `var_p` in a function's own `_requires` / `_ensures`, and `(!var_p)` in body position (a block / `if` `_ensures`, or a `_ghost_stmt`). In an `_inline_pulse` slprop-term position, name the cell `var_p` directly and bind its value via an existential — `$(p)` there is a read action, not a term.
- **View suppression.** Inside inline Pulse the default `_pointer_view` substitution is off, so `$type(node *)` stays the bare `ref node`.
- **Special names.** `this` (inside `_refine*`, the value being refined; reach fields with `this.f`) and `return` (inside `_ensures`, the returned value).

`test/antiquot/antiquot.c` exercises every form.

## Function attributes

- `_pure` — function has no effects; callable in spec position.
- `_rec` — recursive (must be paired with `_decreases`).
- `_pulse_eager_unfold_predicate` — on a struct/union, emit `[@@pulse_eager_unfold]` on the generated `__pred`.

## Global variables

A global is either **pure** (immutable) or **mutable**, and the two are modeled
very differently. A global is pure when *either*:

- it is annotated `_pure`, or
- it is `const`-qualified — this is implicit, no annotation needed
  (`cpp/impl.cpp`: `isConstQualified()`). An initializer is *not* required.

A global with no initializer is still pure if it is `const` or `_pure`: with no
initializer anywhere in the translation unit it is a *tentative definition*
(C11 6.9.2p2) and is initialized as if by `0` (6.7.9p10) — arithmetic types to
zero, pointers to null, aggregates field- and element-wise. That zero is the
value the emitted definition takes, so such a global reads as `0` and PAL can
prove it. An incomplete initializer is filled out the same way, so
`const struct point s = {.x = 1};` reads as `{1, 0}`.

Mutable means a global that is neither `const` nor `_pure`; those are handled by
the bring-your-own-permission model below.

```c
_pure uint32_t g_a = 42;      /* pure, explicit  */
const uint32_t g_b = 7;       /* pure, implicit — same treatment as g_a */
const uint32_t g_c;           /* pure: tentative definition, reads as 0 */
uint32_t       g_d = 1;       /* mutable: not const, not _pure */
```

Because a pure global is immutable, it is not an lvalue: writing it is a
constraint violation in C (6.5.16p2 with 6.3.2.1p1, "not a modifiable lvalue")
and PAL rejects it, as does `_live(g)` — there is no permission to thread.

A pure global lowers to a plain top-level F* value, and every read of it
is **ownership-free** — the read just evaluates to `var_g`, with nothing in the
`requires`:

```fstar
let var_g_b : ty_uint32_t = 7ul
let var_g_c : ty_uint32_t = zero_default     // tentative definition
```

Aggregates are zeroed the same way, element- and field-wise, so
`const uint32_t a[3];` emits
`array_spec_zeroed ty_uint32_t (SizeT.v 3sz) zero_default`.

`extern` is the one case where no value may be assumed. `extern const T g;`
without a definition in this translation unit is a *declaration*, not a
tentative definition: the object lives elsewhere and C constrains its value not
at all. PAL emits `assume val var_g` instead of a zero, so nothing about its
value is provable here.

**Address-of (`&g`)** is supported for scalar and struct globals (pure or
mutable). For a pure global, because reads are ownership-free, any pointer to it
must be read-only forever — a writable alias would let a callee store a value
that PAL-emitted reads do not observe, which is unsound. So alongside `var_g`,
PAL emits

```fstar
assume val addr_var_g : ref ty                          // keyed on the global's identity
assume val addr_var_g_not_null : squash (~(is_null addr_var_g))
assume val acquire_var_g
  : unit -> stt_ghost unit emp_inames emp
      (fun _ -> exists* (p: perm). pts_to addr_var_g #p var_g)
```

The fraction stays existentially quantified, so reads typecheck, writes (which
need `1.0R`) do not, and `&g` may be taken any number of times. A *fixed*
fraction would be unsound to hand out repeatedly: acquiring `k` some `n` times
and gathering yields `n * k`, and `pts_to_perm_bound` (`p <=. 1.0R`) then proves
`False` for `n > 1/k`. `&g` itself is just the address, so it works in any
expression position.

The acquire is an axiom (`assume val`) rather than a proven ghost function: the
ownership is *assumed* to exist, being a fraction of the one reserved for the
global at program start.

Acquiring and releasing that ownership is **explicit**, via `_ghost_stmt`:

```c
uint32_t read_via_addr_of_global(void)
    _ensures(return == 42)
{
    _ghost_stmt(Global_g_const.acquire_var_g_const ());
    const uint32_t *p = &g_const;
    return *p;
    _ghost_stmt(drop_ (exists* q. pts_to Global_g_const.addr_var_g_const #q _));
}
```

The release goes *after* the `return`. A ghost statement in that position is
lowered to `let return_1 = <expr>; <ghosts>; return return_1;`, so the returned
expression is evaluated — still holding the ownership it needs — before the
drop. Releasing earlier would fail if the returned expression reads through the
pointer. This is the same discipline the function-pointer cases use with
`of_fn_div_valid` / `drop_is_valid`.

Omitting either annotation is a verification error (`Leftover resources`, or a
missing-ownership failure at the read), never unsoundness.

Release uses Pulse's generic `drop_`, which resolves unqualified (generated
modules `open Pulse`). Its argument mirrors the acquire's postcondition, but
the stored value and the binder's `perm` type are both inferable, leaving
`drop_ (exists* q. pts_to addr_var_g #q _)`. The two parts that must be written
out are:

- **the ref.** A bare `drop_ _` fails with `Cannot prove: (*?u*)_`, because the
  local holding the address contributes a second `pts_to` and nothing picks
  between them.
- **the existential.** Collapsing it to `drop_ (pts_to addr_var_g #_ _)` fails
  in the SMT solver: the acquire hands out an existentially quantified
  fraction, and a bare `#_` does not stand for one.

Name the bound permission something other than a local in scope (`q` above,
since `p` is the C pointer).

Reads through the pointer yield the same pure value that specs already use, so
`_ensures(return == 42)` follows from `var_g = 42` with no extra reasoning.

`addr_var_g_not_null` gives non-nullness, which does *not* follow from the
points-to alone; use it by comparing the pointer against `NULL` as usual:

```c
bool addr_of_global_is_not_null(void)
    _ensures(return == true)
{
    _ghost_stmt(Global_g_const.acquire_var_g_const ());
    const uint32_t *p = &g_const;
    return p != NULL;
    _ghost_stmt(drop_ (exists* q. pts_to Global_g_const.addr_var_g_const #q _));
}
```

Array globals are out of scope for `&g` (they have no pointer path at all —
`const int *p = g_arr;` is rejected), which keeps the ownership-free
`array_spec_idx` model of `test/global_array_tactic` unaffected.

See `test/addr_global/addr_global.c`.

### Mutable globals: bring your own permission

A mutable global has no pure value — its contents change — so PAL emits *only*
its storage, and no ownership of it. For a scalar or struct global that storage
is the cell at its address (arrays are [below](#mutable-array-globals)):

```fstar
assume val addr_var_g : ref ty
assume val addr_var_g_not_null : squash (~(is_null addr_var_g))
```

There is no `var_g` and, deliberately, no `acquire_var_g`: handing out ownership
of writable storage for free would let two callers each take full permission and
race. Instead the global behaves exactly like a pointer parameter whose
permission the caller supplies — **bring your own permission**. Reads and writes
go through the address (`!addr_var_g`, `addr_var_g := ..`), and every function
that touches `g` names the permission in its contract with `_live(g)`:

```c
uint32_t counter;

void bump(void)
    _requires(_live(counter)) _requires(counter < 100)
    _ensures(_live(counter)) _ensures(counter == _old(counter) + 1)
{
    counter = counter + 1;
}
```

`_live(g)` is `live addr_var_g`, i.e. `exists* v. addr_var_g |-> v`; in spec
position `g` reads as `!addr_var_g`, and `_old(g)` as its pre-state value.
Ownership threads through calls like any other: a caller holding `_live(g)`
hands it to the callee and gets it back.

The permission has to enter the program somewhere, and that somewhere is the
entrypoint: `main` (or whatever the build treats as one) simply *assumes* it in
its `_requires`. Nothing checks that assumption — it is the model's axiom, the
counterpart of the pure global's `acquire_var_g`. Keep the matching `_ensures`,
or Pulse rejects the function for leaking ownership (`Leftover resources`).

```c
int main(void)
    _requires(_live(x)) _requires(_live(counter))
    _ensures(_live(x)) _ensures(_live(counter))
{ ... }
```

Consequences worth knowing:

- A function that omits `_live(g)` does not fail *silently*: the read or write
  fails to verify for want of the `pts_to`, exactly as for a pointer parameter.
- An initializer on a mutable global is ignored; what the storage holds is
  whatever the supplied permission says it holds. State it in a `_requires` if
  a function depends on it.
- Nothing forces two globals' permissions to be held together, and nothing ties
  `_live(g)` to `&g` aliases beyond the fact that `&g` *is* `addr_var_g` — so
  writing through a pointer to `g` while holding `_live(g)` works.

See `test/global_mutable/global_mutable.c`, and
`test/global_non_const_addr/global_non_const_addr.c` for the address-identity
side.

### Mutable array globals

A mutable array global (`T g[N]`, `extern T g[]`, or the `_array T *g` spelling)
is the array *object*, so it is modeled as an assumed handle rather than a cell
at an address, and behaves in every other respect like an `_array T *`
parameter — `g[i]` is `array_read` / `array_write`, `g._length` is
`reveal #nat (length_of var_g)`, and `g` decays to an array pointer:

```fstar
assume val var_g : (array t)
[@@pulse_eager_unfold]
let live_var_g : slprop =
  exists* (s: full_array_lspec t N). array_pts_to var_g 1.0R s
```

`_live(g)` is that named slprop. It is named rather than the library's
`live_array` because it also pins the extent: an `array`'s length lives in its
spec, so `N` can only be stated by the existential's binder. That is what makes

```c
uint32_t buf[4];

void set_last(uint32_t v)
    _requires(_live(buf)) _ensures(_live(buf)) _ensures(buf[3] == v)
{ buf[3] = v; }
```

go through with no length precondition of its own. `1.0R` is full ownership —
unlike a `_pure` global's existential fraction, a mutable array must be
writable, so only one holder of the permission can exist at a time.

When the extent is unknown here (`extern T g[]`, `_array T *g`) the binder is a
plain `full_array_spec`, and a contract that needs the length states it, as for
an array parameter: `_requires(i < g._length)` plus
`_preserves_value(g._length)`.

A *pure* array global is unaffected: it keeps the ownership-free
`full_array_lspec` spec model (`array_spec_idx`), which is why it is excluded
from `&g`.

See `test/global_mutable_array/global_mutable_array.c`.

## See also

- `structs.md` / `unions.md` — what gets generated per struct / union.
- `arrays.md` — the array representation, points-to flavors, and the `_array` / `_arrayptr` distinction.
- `src/pass/emit.rs` — the authoritative lowering when in doubt.
