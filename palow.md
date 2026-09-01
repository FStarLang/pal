# Palow

*Status: draft / design proposal.*

Palow ("PAL, low-level") is a new, lower-level memory model for PAL.

## Motivation

Currently, we pretend that all memory allocations are typed; i.e. that
`(int*) malloc(sizeof(int))` actually allocates a heap cell of type `int`.
This has a number of unfortunate consequences:

 - We cannot give a specification for `malloc`; this function is a built-in
   special case which pattern-matches on the AST to figure out the type
   (`ExprT::Malloc`, `MallocArray`, `MallocFlex` in `src/ir/mod.rs`).
 - We need annotations to determine the F\* type for a variable, i.e. `_array
   int *` becomes an `array int32_t`, `int *` becomes a `ref int32_t`,
   `_core_ref int *` becomes a `core_ref`, etc.
 - We cannot give a good semantics for type-punning, because unions are
   interpreted as heap cells containing an inductive type.
 - We cannot verify custom allocators.
 - Recursive structs need the `_core_ref` escape hatch purely to break F\*
   module/type dependency cycles and non-terminating ownership predicates
   (see `pulse/Pulse.Lib.C.CoreRef.fsti`). A single non-parametric pointer
   type removes the reason for that escape hatch to exist.

## Design overview

Palow is a **base layer**, not a replacement for the current model. Most
generated code, and essentially all user-written specifications, keep working
with typed points-to predicates; those predicates are now *defined* in terms of
byte-level ownership rather than axiomatized. The byte level is there so that
one *can* peek under the hood — to verify a custom allocator, to justify
type-punning, or to relate two views of the same storage — but ordinary code
never has to.

This is the same layering that VST uses (`memory_block` underneath
`data_at`/`field_at`); see [Related work](#related-work).

Rvalue types stay roughly as they are now: integer types are still native F\*
types like `UInt32.t`, structures are still passed around as inductive types,
etc.

However all pointers are now represented as the `ptr` type, no matter whether
they are arrays/references/etc., and no matter what type they point to.

### Layer 0: pointers and bytes

```fstar
val alloc_id : eqtype

// PNVI-style provenance; see "Provenance" below. `None` is the empty
// provenance, i.e. "not derived from any allocation".
type prov = option alloc_id

noeq type byte = {
  value: option UInt8.t;   // None = uninitialized
  prov:  prov;             // provenance of the pointer this byte came from
}

[@@erasable] type bytes = Seq.seq byte

val ptr : Type0
val null : ptr

// Byte offset. Only defined when the result stays within the same object.
val ( +! ) (a: ptr) (n: SizeT.t) : ptr

val mem_pts_to (a: ptr) (p: perm) (b: bytes) : slprop
```

`bytes` is byte-granular rather than bit-granular. Bitfields are then specified
by bit-twiddling on the containing bytes, which is what
`pulse/Pulse.Lib.C.BitField.fst` already does; making every byte a bit sequence
would make every other proof more expensive to pay for one feature.

Every byte carries provenance, not just a value. This is forced: a pointer
stored to memory and read back has to keep its allocation identity, so
provenance necessarily leaks through `bytes`. It is therefore part of the
design from the start rather than something to retrofit.

Core lemmas that everything else is built on:

```fstar
val mem_pts_to_len (a: ptr) (p: perm) (b: bytes)
  : Lemma (requires ...) (ensures v (len b) <= max_object_size)

ghost fn mem_split (a: ptr) (#p: perm) (#b: bytes) (n: SizeT.t)
  requires mem_pts_to a p b ** pure (v n <= v (len b))
  ensures  mem_pts_to a p (slice b 0 n) ** mem_pts_to (a +! n) p (slice b n (len b))

ghost fn mem_join (a: ptr) (#p: perm) (#b1 #b2: bytes) (n: SizeT.t)
  requires mem_pts_to a p b1 ** mem_pts_to (a +! n) p b2 ** pure (len b1 == n)
  ensures  mem_pts_to a p (append b1 b2)

// Two live ranges are disjoint (hence, distinct objects do not alias).
ghost fn mem_pts_to_disjoint (a1 a2: ptr) (#p1 #p2: perm) (#b1 #b2: bytes)
  requires mem_pts_to a1 p1 b1 ** mem_pts_to a2 p2 b2
  ensures  mem_pts_to a1 p1 b1 ** mem_pts_to a2 p2 b2
        ** pure (disjoint_ranges a1 (len b1) a2 (len b2))
```

`mem_split`/`mem_join` are what make custom allocators expressible: handing out
a subrange of a large allocation is just splitting the byte-level resource.

### Provenance

We follow **PNVI-ae-udi** (provenance-not-via-integers, with address-exposure
and user disambiguation), the Cerberus model of de-facto C. A pointer is a
concrete address plus a provenance tag:

```fstar
val addr_of (a: ptr) : GTot SizeT.t
val prov_of (a: ptr) : GTot prov

val ptr_ext (a1 a2: ptr)
  : Lemma (requires addr_of a1 == addr_of a2 /\ prov_of a1 == prov_of a2)
          (ensures  a1 == a2)
```

An access through `a` is only valid when `prov_of a` is the allocation whose
footprint contains the accessed range; `mem_pts_to a p b` carries that
invariant. Pointer arithmetic (`+!`) preserves provenance and is only defined
within the allocation's footprint (plus one-past-the-end).

Because provenance lives in the bytes, `ptr_repr` is *definable* rather than
axiomatized: the bytes of a pointer are the target-endian bytes of its address,
each tagged with the pointer's provenance. Reading a pointer back recovers the
provenance when all the covered bytes agree on it, and the empty provenance
otherwise. Writing a non-pointer type sets the provenance of the bytes it
covers to `None`, and `memcpy` transports provenance along with values — which
is what makes a byte-copied pointer still usable.

The "ae" part is an exposure token, which is duplicable and monotonic:

```fstar
val exposed (i: alloc_id) : slprop   // duplicable

ghost fn expose (a: ptr) (#i: alloc_id) (...)
  ensures exposed i

fn ptr_to_uintptr (a: ptr) (#i: alloc_id) (...)
  returns  n : SizeT.t
  ensures  exposed i ** pure (v n == v (addr_of a))

fn uintptr_to_ptr (n: SizeT.t) (#i: alloc_id)
  requires exposed i ** pure (in_footprint i n)
  returns  a : ptr
  ensures  pure (addr_of a == n /\ prov_of a == Some i)
```

The "udi" part — the nondeterministic choice among several exposed allocations
that could match an address, resolved by how the resulting pointer is later
used — collapses nicely in a verification setting: the caller supplies `i` as a
ghost argument, which *is* the disambiguation, decided statically instead of
by the semantics.

*Alternatives considered.* A flat concrete-address model (no provenance) is
simpler but accepts programs that clang may miscompile, and does not actually
buy much here since the custom-allocator idioms we care about work under PNVI
too — interior pointers inherit the block's provenance. CompCert's
`block * offset`, with no integer address at all, cannot express the
address-arithmetic idioms real allocators use (alignment by masking, metadata
headers recovered by subtraction).

### Layer 1: per-type representation and points-to

For every C type we generate a bytes-to-value relation and a points-to
predicate:

```fstar
// In general not injective: we represent unions as inductives.
// In general not surjective: padding bytes are unspecified.
val uint32_t_repr (x: UInt32.t) (b: bytes) : prop

// Not unfolding:
// - That would pollute the context.
// - To make !(!x) work, we need to be able to resolve the pointee from the
//   context (via the existing [@@@mkey] / has_pts_to machinery).
let uint32_t_pts_to (a: ptr) (p: perm) (x: UInt32.t) : slprop =
  exists* b. mem_pts_to a p b ** pure (uint32_t_repr x b)
```

Non-injectivity of `*_repr` is fine: Pulse points-to predicates *tend* to be
injective, but nothing relies on it (`slprop_pts_to` is not injective either).
It does mean the usual agreement lemma
(`t_pts_to a p x ** t_pts_to a p y ==> x == y`) is a per-type property, proved
where it holds (scalars) and simply absent where it does not (unions).

The existential over `b` is load-bearing: it is exactly what makes padding
bytes unobservable through the typed view. See
[Aggregates and padding](#aggregates-and-padding).

For a scalar type the existential can be dropped, because the representation is
*unique*: an unsigned integer type with no padding bits has exactly one object
representation per value, so `uint32_t_pts_to a p x` is literally
`mem_pts_to a p (encode 4 None (v x))`. The general existential shape is needed
only where the representation is not unique, i.e. aggregates with padding, and
unions.

We need type-specific read and write operations, e.g.

```fstar
fn uint32_t_read (a: ptr) (#p: perm) (#x: UInt32.t)
  requires uint32_t_pts_to a p x
  returns  y : UInt32.t
  ensures  rewrites_to y x
  ensures  uint32_t_pts_to a p x

fn uint32_t_write (a: ptr) (y: UInt32.t) (#x: UInt32.t)
  requires uint32_t_pts_to a 1.0R x
  ensures  uint32_t_pts_to a 1.0R y
```

The `rewrites_to y x` in the read postcondition is what makes nested
dereferences such as `**x` work: the result of the inner read has to be
definitionally connected to the logical pointee so that the outer read can
resolve its own points-to from the context.

### Sizes, alignments and offsets

`sizeof` also becomes **one definition per C type** rather than a function of
the F\* type:

```fstar
val uint32_t_sizeof : SizeT.t
val uint32_t_alignof : SizeT.t
val struct_S_offsetof_f : SizeT.t
```

This replaces `Pulse.Lib.C.Sizeof.c_sizeof : Type u#a -> t` and `c_alignof`,
which are indexed by the *F\* representation type*. That indexing is not just
stylistically different, it is ambiguous: distinct C types can share an F\*
representation (`int` and an enum with `int` as its compatible type, two
typedefs of a struct, etc.), so `c_sizeof` cannot always give the right answer.
Per-C-type constants have no such problem, and PAL already emits several
definitions per type, so the boilerplate cost is marginal.

For every non-variable-size type we then prove

```fstar
val uint32_t_repr_len (x: UInt32.t) (b: bytes)
  : Lemma (requires uint32_t_repr x b) (ensures len b == uint32_t_sizeof)
```

The concrete values come from clang, so generated `.fst` files are
target-dependent — which is already true today (`long` translates to `int64_t`
on Linux and `int32_t` on Windows), so this is not a new constraint, but it
should be documented.

**Implemented.** The clang frontend records the size, alignment and field
offsets of every named C type (`recordTypeLayout`/`recordFieldOffsets` in
`cpp/impl.cpp`) into `ir::LayoutTable`; `src/layout.rs` derives the size of
every other type structurally. `sizeof(T)` and `_Alignof(T)` now emit a plain
`SizeT` literal, which subsumes the old `c_sizeof_*_pos` axioms (positivity is
a computation) and the `c_sizeof_array` axiom (`sizeof(int[8])` is just `32sz`).
`sizeof` inside inline-Pulse annotations, which `src/hauntedc.rs` parses without
a clang AST at hand, resolves through the same table, so specifications and code
agree by construction.

### Permissions

Fractional permissions apply to whole objects, not to individual bytes:
`mem_pts_to a p b` carries a single `p` for the entire range. To get different
fractions for different parts of a structure, split the permission on the
*structure* into permissions on its *fields* (as today, and as VST's `field_at`
does), not into per-byte fractions.

### Allocation

`freeable` stays largely as it is, but must record how much memory is being
returned, since the pointer no longer carries a type:

```fstar
val freeable (a: ptr) (n: SizeT.t) : slprop

fn malloc (n: SizeT.t)
  returns  a : ptr
  ensures  (if is_null a then emp
            else exists* b. mem_pts_to a 1.0R b ** freeable a n ** pure (len b == n))

fn free (a: ptr) (#n: SizeT.t) (#b: bytes)
  requires freeable a n ** mem_pts_to a 1.0R b ** pure (len b == n)
```

With this, `malloc` is an ordinary function with an ordinary specification, and
the `Malloc`/`MallocArray`/`MallocFlex` IR nodes and their emit-time special
cases can be deleted. A custom `xmalloc` is specified by writing the same
postcondition.

`freeable` does **not** split. A pool allocator that carves a block into
chunks hands out its own `pool_freeable` predicate instead, which is what stops
a caller from passing a `pool_malloc`'d pointer to `free`. Keeping the two
predicates distinct is a feature, not a limitation.

### Local variables

Local variables get per-type stack allocation and deallocation functions,
paired with `defer` to ensure they don't escape:

```fstar
fn uint32_t_stack_alloc ()
  returns  a : ptr
  ensures  uint32_t_pts_to_uninit a

fn uint32_t_stack_free (a: ptr)
  requires uint32_t_pts_to_uninit a
```

There is deliberately no token pairing an allocation with its deallocator, the
same design Pulse's own `let mut` uses. Passing a `malloc`ed pointer to
`uint32_t_stack_free` would be wrong, but PAL controls the translation and
never emits it, so the token would cost ownership bookkeeping everywhere to
rule out a program we do not generate.

We deliberately do *not* fall back to Pulse locals for the non-address-taken
cases: they behave quite differently, and having two kinds of local in the
translator would be a permanent source of special cases. With dedicated
per-type stack alloc/free the performance impact should be small; if it isn't,
the right fix is upstream in Pulse rather than a second local-variable
mechanism here.

### Aggregates and padding

A structure's `*_repr` decomposes into its fields' `*_repr`s at the
clang-computed offsets, with the padding bytes left unconstrained:

```fstar
// struct S { uint32_t f; uint8_t g; };  // sizeof 8, offsetof g = 4
val struct_S_repr_intro (x: struct_S) (b bf bg bpad: bytes)
  : Lemma (requires b == bf @| bg @| bpad /\
                    uint32_t_repr x.f bf /\ uint8_t_repr x.g bg)
          (ensures struct_S_repr x b)
```

and correspondingly a ghost split/join pair taking `struct_S_pts_to a p x` to
`uint32_t_pts_to a p x.f ** uint8_t_pts_to (a +! 4sz) p x.g ** mem_pts_to (a +! 5sz) p pad`.

Two consequences worth stating explicitly:

- **Writing an aggregate havocs its padding.** C leaves padding bytes
  unspecified after a struct assignment, and the model matches that for free:
  since `struct_S_pts_to` only asserts that *some* `b` represents `x`, nothing
  about the padding survives a write. Code that stashes data in padding bytes
  and expects it to survive a whole-struct assignment will not verify — which
  is correct.
- **Unions** are represented as inductives, as today, so `*_repr` for a union
  relates one value to the bytes of whichever member it holds. This is where
  non-injectivity comes from, and it is what makes type-punning expressible:
  the same bytes may be related to several union values.

### Arrays

An array of `n` elements of type `t` is a combinator over the element's
representation, with stride `t_sizeof`:

```fstar
let array_repr (t_repr: 'a -> bytes -> prop) (t_sizeof: SizeT.t)
               (xs: Seq.seq 'a) (b: bytes) : prop =
  len b == t_sizeof *! len xs /\
  (forall (i: nat). i < Seq.length xs ==>
     t_repr (Seq.index xs i) (slice b (t_sizeof *! i) (t_sizeof *! (i + 1))))
```

so we do not need a per-array-type axiomatization, and the existing
`mem_split`/`mem_join` give array splitting for free. Flexible array members —
today a dedicated `MallocFlex` special case — become an ordinary struct
followed by an `array_repr` chunk, with no special support in the translator.

### Effective types

C's effective-type rules (C11 6.5p6-7) are what license a compiler's
type-based alias analysis. Ignoring them is *permissive*: we would verify
programs that clang may miscompile. Since ignoring them never blocks a
verification, this can be staged last — but the design should reserve room for
it now, because retrofitting an index onto `mem_pts_to` later is disruptive.

Proposal: carry a per-byte effective-type map alongside the bytes.

```fstar
noeq type ctype =                    // generated descriptors, one per C type
  | TChar | TInt32 | TUInt32 | ...
  | TPtr
  | TStruct of string
  | TUnion  of string
  | TArray  of ctype & nat

noeq type etype_entry = {
  ty:    ctype;   // the type of the object living here
  off:   SizeT.t; // this byte's offset within that object
  fixed: bool;    // true for declared objects, false for allocated storage
}

type etypes = Seq.seq (option etype_entry)   // None = no effective type yet

val mem_pts_to (a: ptr) (p: perm) (b: bytes) (e: etypes) : slprop
```

Access rules:

- **Read at type `t`** requires every covered entry to be *compatible* with
  `t`, where `compatible` holds if the entry is `None`, or `t` is a character
  type, or `t` is the type of the subobject of `entry.ty` at `entry.off`
  (which covers the union case: accessing any member of a union object is
  permitted, and this is precisely what makes acceptance test 2 go through).
- **Write at type `t`** requires the same, and *sets* the entries to `t` when
  they are `None` or `fixed = false` (allocated storage takes its effective
  type from the last store); accesses through a character type do not change
  the effective type.
- **`memcpy` and character-wise copies** transport the entries along with the
  bytes, matching the C rule that a byte-copied object inherits the source's
  effective type.
- Declared objects (`fixed = true`) get their entries at allocation and keep
  them for their lifetime.

First cut: instantiate `etypes = unit` and make every rule trivially true. The
typed layer's interface does not mention `etypes` at all, so turning the
tracking on later only affects layer 0 and the aggregate lemmas.

## Consequences for the translator

- `_core_ref` disappears. Its only purpose is to break type- and
  predicate-level cycles for recursive structs; a non-parametric `ptr` has no
  cycles to break.
- `_array` / `_arrayptr` no longer change the F\* *type* of a variable (it is
  `ptr` either way), only which points-to predicate a specification mentions.
  This removes the type-mismatch class of errors that pointer-kind inference in
  `src/pass/elab.rs` exists to avoid.
- `ExprT::Malloc`, `MallocArray` and `MallocFlex` and their emit special cases
  are deleted.
- `Pulse.Lib.C.Sizeof` (F\*-type-indexed) is replaced by per-C-type constants.
  **Done:** the module is gone, and `sizeof`/`_Alignof` translate to literals.

## Open questions

 - How much of the proof cost of the extra indirection can be hidden? The
   typed layer should be close to as cheap to use as today's axiomatized
   `pts_to`; where it isn't, the preferred fix is upstream in Pulse.
 - Variable-length arrays and variably-modified types: does `*_sizeof` need to
   become a function in some cases?
 - How much of PNVI-ae-udi do we need up front? Provenance in `bytes` and on
   `ptr` is required from day one; the `exposed` machinery is only needed once
   we translate `uintptr_t` round-trips.
 - `volatile`, `restrict`, `const`, and atomics are out of scope for now.

## Related work

| System | Pointer model | Bytes | Effective types | Layering |
| --- | --- | --- | --- | --- |
| CompCert (Leroy & Blazy, JAR 2008) | `block * offset` | `Undef \| Byte \| Fragment` | no | flat |
| CH₂O (Krebbers, 2015) | provenance + memory trees | bit-level, with pointer bits | yes, via union tags | flat |
| Cerberus / PNVI (Memarian et al., POPL 2019) | provenance, several variants | byte + provenance | partially | flat |
| VIP (Lepigre et al., POPL 2022) | address + "exposed" discipline | bytes | no | tailored to allocator idioms |
| VST (Appel et al.) | CompCert's | CompCert's | no | `memory_block` → `data_at`/`field_at` |
| RefinedC (Sammler et al., PLDI 2021) | Caesium (CompCert-like) | bytes | no | layout types → refined ownership types |
| Low\* / Pulse (today) | typed, parametric `ref a` | none | n/a | flat, typed only |
| **Palow** | PNVI-ae-udi | `option UInt8.t` + provenance | staged, see above | `mem_pts_to` → `t_pts_to` |

The closest fit is **VST**: `memory_block sh n p` underneath
`data_at sh t v p`, with `field_at` for field-granular shares, is almost
exactly the `mem_pts_to` / `t_pts_to` / struct-split structure proposed here,
and is good evidence that the layering scales to real programs.

**Cerberus/PNVI** is the model we adopt. **VIP** is the most relevant point of
comparison for the custom-allocator acceptance test: it was designed
specifically to verify real-world C idioms involving integer-pointer casts, and
is a useful sanity check on whether our `exposed` discipline is ergonomic
enough for the allocator we want to write.

**CH₂O** is the reference for effective types; the proposal above is a
flattened, per-byte version of its memory trees, chosen because our aggregates
are already flattened into `bytes`.

## Acceptance tests

 - `malloc` is no longer a special built-in; we can give a spec to a custom
   `xmalloc` function and use it just like `malloc` today.
 - We can prove
   ```c
   union { int x; struct { int y; int z; }; } a; a.x = 10;
   int b = a.y; _ghost_stmt(...); _assert(b == 10);
   ```
 - We can write a custom allocator that first allocates some number of bytes
   and then hands out pointers into that range, and it is usable just like
   `malloc` today. The allocator exposes its own `pool_freeable` predicate, so
   passing a `pool_malloc`'d pointer to `free` does not verify.
 - `_core_ref` is deleted, and the recursive-struct tests that motivated it
   still verify.
 - We can write `memcpy` between two objects of different types and relate the
   results at both types, including transporting a stored pointer's provenance
   through the copy.
 - The existing `test/` suite still verifies, with no annotation churn beyond
   the mechanical removal of `_core_ref`.

## Evaluating the cost

The purpose of this refactor is to evaluate whether a lower-level memory model
is *feasible* for PAL, so the outcome we want is a number, not a pass/fail
gate. An increase in verification time or annotation overhead may well be worth
paying for verifiable custom allocators and a real account of type-punning —
but we should know what we are paying.

Measure, before and after, over the whole `test/` suite:

 - total and per-file F\* verification time;
 - number of Z3 queries and rlimit consumed;
 - lines of annotation in the `.c` inputs, and lines of generated `.fst`;
 - number of `_include_pulse` / manual-proof escape hatches needed.

Record the numbers in this document when the evaluation is done.

## Implementation status

Milestone 1 is implemented in `pulse/`, together with enough of milestones 2, 4
and 6 to check that the layering actually works. Everything below verifies as
part of `make -C pulse`.

| Module | Kind | Contents |
| --- | --- | --- |
| `Pulse.Lib.C.Palow.Bytes` | proved | `alloc_id`, `prov`, `byte`, `bytes`, `uninit`/`zeroed`, `strip_prov`, slice/append lemmas |
| `Pulse.Lib.C.Palow.Ptr` | axiomatized | `ptr`, `addr_of`, `prov_of`, `ptr_ext`, `( +! )`, `disjoint_ranges` |
| `Pulse.Lib.C.Palow` | axiomatized | `mem_pts_to`, `mem_split`/`mem_join`, disjointness, injectivity, share/gather |
| `Pulse.Lib.C.Palow.Encoding` | proved | little-endian `encode`/`decode`, round-trip and injectivity |
| `Pulse.Lib.C.Palow.Scalar` | proved | `uint8_t`/`uint32_t` `*_repr`, `*_pts_to`, `*_sizeof`, agreement, share/gather, reveal/conceal |
| `Pulse.Lib.C.Palow.Nullable` | proved | `unless_null` with its intro/elim pair |
| `Pulse.Lib.C.Palow.Alloc` | axiomatized | `freeable`, `malloc`, `calloc`, `free` |
| `Pulse.Lib.C.Palow.Machine` | axiomatized | typed loads/stores, stack alloc/free |
| `Pulse.Lib.C.Palow.Aggregate` | proved | `struct S { uint32_t f; uint8_t g; }` with padding, field split/join |
| `Pulse.Lib.C.Palow.Pool` | proved | bump allocator handing out `uint32_t`s from a byte range |

Two results are worth calling out, because they are the ones that would have
sunk the design:

- **Field split/join for a struct with padding is provable from `mem_split` and
  `mem_join` alone.** PAL can therefore *generate* these lemmas per struct
  rather than axiomatizing an ownership predicate per struct as it does today.
- **The bump allocator needs no new axioms.** `pool_alloc_uint32` is an
  ordinary Pulse function; its proof is "split the remaining range at four
  bytes, keep the tail in the invariant, claim the head". Under the current
  model the program cannot even be stated. Note also that the pool hands out
  bare `uint32_t_pts_to_uninit` and never `Alloc.freeable`, so calling `free`
  on a chunk is unprovable -- which is precisely why `freeable` does not split.

Milestone 3 is the first change to the translator itself, and it is done: sizes
and alignments no longer go through `Pulse.Lib.C.Sizeof` (deleted) but are taken
from clang and emitted as literals. The plumbing is `ir::LayoutTable` (filled by
`cpp/impl.cpp`), `src/layout.rs` (structural sizing) and `emit_layout_const` in
`src/pass/emit.rs`.

Not yet implemented: the `exposed`/`uintptr_t` discipline, effective types,
arrays, unions, and the remaining translator changes. `Machine` and `Alloc` are
axiomatized because their operations are machine primitives, but note that
their *specifications* are written entirely in terms of the derived layer-1
predicates, so they add operations rather than new facts about memory.

### Known deviations

- `( +! )` is total, so forming an out-of-bounds pointer is not itself
  rejected; only out-of-bounds *access* is, because `mem_pts_to` is available
  only for in-bounds ranges. This is strictly more permissive than ISO C.
- `mem_pts_to_disjoint` requires one side to be exclusively owned rather than
  the general `~(p1 +. p2 <=. 1.0R)`. Writes need full permission anyway, and
  the restricted form is far easier for the prover to apply.

## Milestones

1. **Done.** Layer 0: `ptr` with provenance, `bytes`, `mem_pts_to`, split/join/
   disjointness. No translator changes.
2. *In progress.* Re-derive the scalar typed layer on top, including per-type
   stack alloc/free and `rewrites_to` on reads (done); switch the translator to
   emit `t_pts_to` (not started). Existing scalar tests pass.
3. **Done for `sizeof`/`alignof`.** Sizes and alignments now come from clang's
   target ABI and are emitted as concrete `SizeT` literals;
   `Pulse.Lib.C.Sizeof` is deleted. Field offsets are collected from clang too
   but are not consumed yet — they are what milestone 4 needs.
4. *In progress.* Aggregates: struct `*_repr`, field split/join and padding are
   done for one worked example; unions and generated-per-struct lemmas are not.
5. `malloc`/`calloc`/`free` as ordinary specifications (specs done); delete the
   AST special cases; delete `_core_ref`.
6. *Done for the model.* Custom allocators, with their own `freeable`
   predicates.
7. `exposed` / `uintptr_t` round-trips.
8. Effective types.
