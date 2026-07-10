# PAL documentation

To verify a C program with PAL you need to know two things: how to express what your program is supposed to do, and how the C constructs you use are represented in Pulse.

## Writing specifications

Specifications are written as macros (`_requires`, `_ensures`, `_invariant`, …) declared in `pal.h` and placed inline with the C code. Under `-DC2PULSE` they expand to Clang annotations PAL reads; otherwise they vanish and the file still compiles as plain C.

For the full annotation reference, see [`pal_surface_syntax.md`](pal_surface_syntax.md).

## How data is modelled

Scalar types are the easy case: `int`, `unsigned`, `char`, … map directly to F* integer types (`Int32.t`, `UInt32.t`, …) and are passed by value with no ownership tracking. A pointer to a scalar (`T*`) becomes `ref T` paired with a `pts_to` slprop.

Compound types need more machinery because they combine a runtime value with the resources it owns. Each has its own doc:

- [`arrays.md`](arrays.md) — array representation, the three points-to flavors, and the `_array` / `_arrayptr` distinction.
- [`structs.md`](structs.md) — what gets emitted per `struct`.
- [`unions.md`](unions.md) — what gets emitted per `union`.

## Proving and internals

- [`skill.md`](skill.md) — a practical guide to writing specs and progressing proofs with PAL.
- [`internals.md`](internals.md) — how PAL translates C into Pulse/F*: the compiler pipeline, IR, diagnostics, and output layout.
