# PAL documentation

To verify a C program with PAL you need to know two things: how to express what your program is supposed to do, and how the C constructs you use are represented in Pulse.

## Writing specifications

Specifications are written as macros (`_requires`, `_ensures`, `_invariant`, …) declared in `pal.h` and placed inline with the C code. Under `-DC2PULSE` they expand to Clang annotations PAL reads; otherwise they vanish and the file still compiles as plain C.

For the full annotation reference, see [`pal_surface_syntax.md`](pal_surface_syntax.md).

## How data is modelled

PAL translates against the Palow memory model: memory is bytes, a pointer is an address plus a provenance, and every C type's points-to predicate is defined in terms of byte-level ownership. Scalars, structs, unions and arrays are all described in [`palow.md`](../palow.md), which is both the design document and the implementation log.

## Proving and internals

- [`skill.md`](skill.md) — A skill for getting agents to work with PAL
- [`internals.md`](internals.md) — how PAL translates C into Pulse/F*: the compiler pipeline, IR, diagnostics, and output layout.
