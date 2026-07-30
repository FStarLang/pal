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

A refinement does *not* change the runtime representation. It is attached to the **type** at every site where the type appears (parameter, struct field, return value, …) and is materialised as an extra pure conjunct in any slprop emitted for a value of that type — i.e. in the implicit `pts_to` of a function parameter, in a struct's `__pred`, etc.

**On a typedef** — the refinement fires for every use of the typedef.

```c
_refine(this._length == 32) typedef _array uint8_t *uds_array;

void f(uds_array a) { ... }
// requires: array_pts_to_full var_a 1.0R val_a_0 ** pure (length_of var_a == 32)
```

`_refine_always` on a typedef is the form to use when the type also appears in `_out` position, since the refinement then has to hold in the uninit precondition too.

**On a struct declaration** — `this` is the whole record; reach into fields with `this.<field>`. Just like a typedef refinement, the refinement is carried by the struct type and so fires at every use of `struct S`; `struct_S__pred` itself is unchanged. The annotation must be written *after* the `struct` keyword, otherwise clang ignores it.

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

- `_ghost_arg(T)` — extra parameter erased at runtime; usable only in specs and ghost statements.
- `_ghost_stmt(expr)` — Pulse statement executed only during verification (e.g. applying a lemma).

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

## See also

- `structs.md` / `unions.md` — what gets generated per struct / union.
- `arrays.md` — the array representation, points-to flavors, and the `_array` / `_arrayptr` distinction.
- `src/pass/emit.rs` — the authoritative lowering when in doubt.
