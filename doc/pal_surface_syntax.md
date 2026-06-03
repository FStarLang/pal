# PAL surface syntax

PAL programs are C files annotated with macros declared in `pal.h`. Under `-DC2PULSE` each macro expands to a Clang `__attribute__((annotate("pal-...")))`; without it the macros vanish and the file compiles as ordinary C.

A function's verification contract has three layers, applied in this order:

1. **Default ownership** — for every non-`_plain` parameter PAL implicitly threads an in-memory resource (e.g. `pts_to`, `array_pts_to_full`) into both `requires` and `ensures`.
2. **User contracts** — `_requires` / `_ensures` / `_invariant` / `_refine*` add pure or spatial predicates over those resources.
3. **Ghost glue** — `_ghost_arg`, `_ghost_stmt`, `_assert`, `_inline_pulse`, `_include_pulse` reach the Pulse layer directly when the surface syntax isn't enough.

To suppress the default ownership for one parameter, prefix it with `_plain`.

## Default contract per parameter shape

| C syntax                  | implicit resource in `requires` / `ensures`         |
|---------------------------|-----------------------------------------------------|
| `T x` (scalar)            | none                                                |
| `_plain T x`              | none                                                |
| `T *x`                    | `pts_to var_x #1.0R val_x_0`                        |
| `_consumes T *x`          | `pts_to` in `requires` only — not returned          |
| `_out T *x`               | `pts_to_uninit` in `requires`, `pts_to` in `ensures`|
| `_array T *x` / `T x[]`   | `array_pts_to_full var_x 1.0R val_x_0`              |
| `_arrayptr T *x`          | `arrayptr_pts_to var_x parent`                      |
| `struct S *x`             | `pts_to var_x` plus `struct_S__pred (!var_x) p`     |

## User-written contracts

- `_requires(p)` / `_ensures(p)` — extra pre / post predicates.
- `_preserves(p)` = `_requires(p) _ensures(p)`.
- `_preserves_value(x)` = `_ensures(x == _old(x))`.
- `_invariant(p)` — loop invariant (one per `_invariant`, may repeat).
- `_decreases(p)` — termination measure; required for `_rec` functions.
- `_assert(p)` — verification assertion inside a function body.

## Refinement types

Type-level predicates carried with a value. The value is named `this` inside the predicate.

| annotation                  | when the predicate must hold              |
|-----------------------------|-------------------------------------------|
| `_refine(p)`                | when the value is initialized             |
| `_refine_always(p)`         | always, even when uninitialised           |
| `_refine_uninit(p)`         | only when uninitialised                   |
| `_refine_value(bind, pred)` | as `_refine`, but binding name is `bind`  |

## Spec-language expressions

Valid only inside `_requires` / `_ensures` / `_invariant` / `_refine*` / `_assert` / `_ghost_stmt`:

- `_old(x)` — value of `x` at function entry.
- `_live(x)` — slprop asserting `x`'s resource is currently owned.
- `x._length` — runtime length of an array.
- `_specint` — arbitrary-precision integer (ghost arithmetic).
- `_slprop` — type cast used in `_refine` to declare a separation-logic predicate.
- `$(x)` — antiquotation: splice a C-level identifier into an `_inline_pulse` body.

## Ghost code

- `_ghost_arg(T)` — extra parameter erased at runtime; usable only in specs and ghost statements.
- `_ghost_stmt(expr)` — Pulse statement executed only during verification (e.g. applying a lemma).

## Pulse interop

- `_inline_pulse(expr)` — embed a Pulse expression in a spec position.
- `_include_pulse(Mod, snippet)` — drop a verbatim Pulse block (definitions, lemmas, helpers) into a module `Mod`.
- `_let(sig, body)` / `_let_rec(sig, body)` / `_letimpure(sig, body)` — Pulse-level top-level bindings.
- `_type(name, body)` — Pulse-level type definition.

## Function attributes

- `_pure` — function has no effects; callable in spec position.
- `_rec` — recursive (must be paired with `_decreases`).
- `_pulse_eager_unfold_predicate` — on a struct/union, emit `[@@pulse_eager_unfold]` on the generated `__pred`.

## See also

- `structs.md` / `unions.md` — what gets generated per struct / union.
- `arrays.md` — the array representation, points-to flavors, and the `_array` / `_arrayptr` distinction.
- `src/pass/emit.rs` — the authoritative lowering when in doubt.
