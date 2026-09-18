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
val exposed (q: prov) : slprop   // duplicable
val in_footprint (q: prov) (x: nat) : prop

ghost fn expose (a: ptr) (#p: perm) (#b: bytes)
  preserves mem_pts_to a p b
  requires  pure (len b > 0)
  ensures   exposed (prov_of a)

fn ptr_to_uintptr (a: ptr)
  preserves exposed (prov_of a)
  returns   n : SizeT.t
  ensures   pure (SizeT.v n == addr_of a)

fn uintptr_to_ptr (n: SizeT.t) (q: erased prov)
  preserves exposed q
  requires  pure (in_footprint q (SizeT.v n))
  returns   a : ptr
  ensures   pure (addr_of a == SizeT.v n /\ prov_of a == reveal q)
```

Both are indexed by a `prov` rather than an `alloc_id` so that every signature
can be written in terms of `prov_of a` without a `Some?` refinement on the
binder. `exposed None` is harmless: it is `in_footprint` that decides whether an
integer can become a *usable* pointer, and `in_footprint None x` is never
provable, because the only way to establish `in_footprint` is from ownership,
and ownership implies a real allocation.

The "udi" part — the nondeterministic choice among several exposed allocations
that could match an address, resolved by how the resulting pointer is later
used — collapses nicely in a verification setting: the caller supplies `q` as a
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

**Implemented.** `Pulse.Lib.C.Palow.Etype` defines the vocabulary and the
access rules, and proves the facts that decide whether they are usable:
reading a `uint32_t` out of a `union U` object is allowed at *both* member
offsets (so acceptance test 2 survives), an array is readable element by
element, and reading a pointer out of storage whose last store was an integer
is not allowed. `access_ok` is defined by cases over a closed `ctype`, which is
exactly the shape a code generator emits; the enumeration is instantiated here
at the types the rest of the model uses.

Layer 0 reserves the index as `mem_pts_to_at`, with `mem_recall`/`mem_forget`
and index-aware split/join. In this first cut the index is present but not
enforced: recall and forget together make `mem_pts_to a p b` equivalent to
`exists* e. mem_pts_to_at a p b e`, so no layer-1 predicate has to mention one
and no existing proof changes. Switching enforcement on means deleting
`mem_recall`'s unconstrained form and making the typed loads and stores in
`Machine` demand `read_ok` and produce `store_etypes`. That change is confined
to layer 0 and `Machine`: the aggregate, array and union lemmas never mention
the index, because splitting bytes splits the index alongside them.

The reason to do this before the translator port rather than after is that it
is the one change to layer 0 that cannot be made cheaply later -- adding an
index to `mem_pts_to` touches every module in the stack.

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

### First measurements

Taken with the port at the state described under "Implementation status":
specifications for every function whose types the model covers, and bodies for
straight-line scalar code. The Palow side is therefore *partial*, and the
numbers below are not a verdict. What they are good for is ruling out the
failure mode we were most worried about — that a byte-level model would be
ruinously slow — and identifying what actually dominates the cost today.

Whole `test/` suite, from a clean cache:

| | current model | Palow (partial) |
| --- | --- | --- |
| wall time | 3 m 54 s (`-j8`) | 2.5 s (`-j256`) |
| CPU time | 23 m 13 s | 2 m 28 s |
| generated modules | 2358 | 158 |
| generated lines | 53 350 | 10 556 |

Two comparable single tests, controlling for what is actually being verified:

| | current model | Palow |
| --- | --- | --- |
| `swap` (1 function) | 1.75 s, 3 modules, 31 lines | 0.70 s, 1 module, 52 lines |
| `issue51_test` (60 functions) | 89.7 s, 137 modules, 1762 lines | 1.34 s, 1 module, 513 lines |

`issue51_test` is the useful one: all 60 of its functions are translated with
real bodies and none are skipped, so the two columns verify the same program.

### What the numbers say

**Verification cost is dominated by module granularity, not by the memory
model.** F\* spends about 0.65–0.85 s on a generated module regardless of its
contents: an eleven-line `Func_cmp1.fst` from `issue51_test` takes 844 ms on
its own, and an empty module with no Pulse in scope still takes 238 ms. PAL
emits one module per declaration, so `issue51_test`'s 89.7 s is roughly
137 × 0.65 s of fixed cost. The Palow emitter happens to produce one module per
translation unit, which is why it looks 67× faster; almost all of that is
packaging. Anyone repeating this measurement later must control for it, and it
is worth asking separately whether the current one-module-per-declaration
scheme is paying for itself.

**Byte-level reasoning did not show up as a cost.** The scalar layer folds to a
single `mem_pts_to` with a concrete `encode`, and the derived lemmas discharge
without visible solver effort. The `pulse/` library itself — including the
proved `Encoding`, `Aggregate`, `Union`, `Etype` and `Provenance` modules —
verifies as part of the ordinary build.

**Generated code is smaller per function**, though not by as much as the table
suggests. `issue51_test` is 29 lines per function today against about 8 for
Palow. Some of that is real — no pointer-kind-specific predicate, one `ptr`
type instead of a family — and some is the untranslated contracts. Now that
Palow also emits one module per declaration it pays the same module preamble
the old translator does, so that part of the saving is gone.

**Verification time is about 2.5x better, not thirtyfold.** `issue51_test`:
1m30 old against 35s Palow, over the same 60 functions and the same 60
modules. An earlier measurement of 1.2s was comparing 139 F\* invocations
against one, and measured startup rather than proof.

### Still to measure

These need the port to be further along to mean anything:

 - Z3 queries and rlimit consumed. `--query_stats` reports nothing on a
   successful run in this build, so this needs a different harness.
 - Annotation lines in the `.c` inputs. Today's suite has 28 829 lines of C
   and headers, 4092 of which mention a PAL annotation, and 341
   `_include_pulse` uses. The question the refactor has to answer is whether
   those numbers go up, and the `_include_pulse` count is the one to watch: it
   is the escape hatch, and every use is a place the model was not expressive
   enough. All 341 are currently untranslated, so we do not know yet.
 - Verification time for aggregates, which is where a byte-level model is most
   likely to hurt — a struct's points-to unfolds to a `mem_pts_to` over a
   concrete byte layout, and nothing in the suite exercises that at scale yet.

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
| `Pulse.Lib.C.Palow.Scalar` | proved | `uint8_t`/`uint32_t`/stored-pointer `*_repr`, `*_pts_to`, `*_sizeof`, agreement, share/gather, reveal/conceal |
| `Pulse.Lib.C.Palow.Nullable` | proved | `unless_null` with its intro/elim pair |
| `Pulse.Lib.C.Palow.Alloc` | axiomatized | `freeable`, `malloc`, `calloc`, `free` |
| `Pulse.Lib.C.Palow.Machine` | axiomatized | typed loads/stores, `memcpy`, stack alloc/free |
| `Pulse.Lib.C.Palow.Expose` | axiomatized | `exposed`, `in_footprint`, `expose`, `ptr_to_uintptr`, `uintptr_to_ptr` |
| `Pulse.Lib.C.Palow.Provenance` | proved | the `uintptr_t` round trip, and `memcpy` transporting a stored pointer |
| `Pulse.Lib.C.Palow.CTypes` | proved | the remaining C scalar types (`_Bool`, `int8_t`..`int64_t`, `uint16_t`, `uint64_t`, `size_t`, `uint8_t`'s derived set) |
| `Pulse.Lib.C.Palow.Examples` | proved | hand-written Palow renditions of programs PAL already translates |
| `Pulse.Lib.C.Palow.Etype` | proved | `ctype`, per-byte effective-type entries, `access_ok`, the store rule, and the union/array/punning theorems |
| `Pulse.Lib.C.Palow.Aggregate` | proved | two structs (with and without padding), field split/join, flexible array members |
| `Pulse.Lib.C.Palow.Array` | proved | generic `array_repr`/`array_pts_to`, split/join, per-element focus |
| `Pulse.Lib.C.Palow.Union` | proved | `union U { uint32_t x; struct T t; }`, member views, the type-punning acceptance test |
| `Pulse.Lib.C.Palow.Pool` | proved | bump allocator handing out `uint32_t`s from a byte range |

Eight results are worth calling out, because they are the ones that would have
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
- **Type punning through a union verifies.** Acceptance test 2 is an ordinary
  Pulse program: store through `.x`, load through `.y`, and the value survives.
  Two variants are proved, one where the union's trailing bytes are never
  initialized (so `.z` is not readable, but `.y` is) and one where the union
  really holds its struct member. Nothing about it is union-specific machinery;
  both members name the same bytes, so both member views produce the same
  resource at the same address.
- **Arrays need no per-type definitions at all.** `array_repr` is a combinator
  over the element's own `t_repr` and size, so PAL emits nothing for `T[N]`,
  and `array_focus` -- ownership of `a[i]` at `a + sizeof(T) * i` -- is two
  `mem_split`s. Flexible array members fall out as a struct predicate
  conjoined with an `array_pts_to` at the header's size, with no `MallocFlex`
  special case and no ghost length field pinned inside the record.
- **`ptr_repr` is a definition, not an axiom.** A stored pointer's object
  representation is the little-endian bytes of its address, each tagged with
  the pointer's provenance. Injectivity (a stored pointer is recovered exactly,
  provenance included) and the fact that an integer store destroys it (integer
  representations are provenance-free) are then both consequences of that one
  definition rather than two separate assumptions.
- **`memcpy` transports provenance for free.** Its specification says only that
  the destination ends up holding the same *bytes*; because bytes carry
  provenance, a pointer copied byte-wise stays dereferenceable, and acceptance
  test 5 is an ordinary Pulse program. Under a model where the object
  representation is a sequence of plain `uint8_t`s this program is not
  provable at all, and no strengthening of `memcpy`'s spec short of adding
  provenance to bytes would make it so.
- **Effective types do not conflict with type punning through a union.** The
  worry was that adding C11 6.5p7 would retract acceptance test 2. It does not:
  the union rule is "every member is accessible at offset 0", so `.x` and
  `.t.z` are both readable, and the proof is by computation. What the rules
  *do* reject is the case they are supposed to reject -- reading a pointer out
  of storage whose last store was an integer.
- **The per-type emission strategy costs about 105 lines per C scalar type,
  and none of it is an axiom.** `Pulse.Lib.C.Palow.CTypes` covers `_Bool`,
  `int8_t` through `int64_t`, `uint16_t` and `uint64_t` in 849 lines, generated
  mechanically from a table of (name, F* type, size, signedness) -- exactly the
  information the translator has. Signed types differ from unsigned ones only
  in composing `Encoding.to_bits`, `_Bool` only in mapping `true`/`false` to
  1/0, and the seven derived resource lemmas are textually identical for every
  type. Every one of the eight type groups verified on the first attempt, which
  is the evidence that mattered: if the derivation had needed per-type
  ingenuity, per-type emission would not be viable.

Milestone 3 is the first change to the translator itself, and it is done: sizes
and alignments no longer go through `Pulse.Lib.C.Sizeof` (deleted) but are taken
from clang and emitted as literals. The plumbing is `ir::LayoutTable` (filled by
`cpp/impl.cpp`), `src/layout.rs` (structural sizing) and `emit_layout_const` in
`src/pass/emit.rs`.

Milestone 7 is done in the model. `Expose` is axiomatized -- exposure is a
property of the machine and its allocator, not of any program -- but the two
theorems that give it content are proved in `Provenance`: the `uintptr_t` round
trip returns the pointer you started with, and `memcpy` preserves a stored
pointer's usability.

Milestone 8 is done for the model: the rules are defined and proved, and layer
0 carries the index, but nothing enforces it yet -- see the effective-types
section for what switching it on costs.

Not yet implemented: the remaining translator changes.
`Machine`, `Alloc` and `Expose` are axiomatized because their operations are
machine primitives, but note that their *specifications* are written entirely
in terms of the derived layer-1 predicates, so they add operations rather than
new facts about memory.

### Known deviations

- `( +! )` is total, so forming an out-of-bounds pointer is not itself
  rejected; only out-of-bounds *access* is, because `mem_pts_to` is available
  only for in-bounds ranges. This is strictly more permissive than ISO C.
- `mem_pts_to_disjoint` requires one side to be exclusively owned rather than
  the general `~(p1 +. p2 <=. 1.0R)`. Writes need full permission anyway, and
  the restricted form is far easier for the prover to apply.
- Addresses are assumed to fit in 64 bits (`Ptr.addr_bound`), so that a stored
  pointer's address round-trips through `ptr_sizeof` bytes. This is a target
  property, and is the same LP64 assumption the scalar sizes already make.
  It cannot be derived from `SizeT.fits`, which is abstract.
- `uint8_t_pts_to` requires provenance-free bytes, so a pointer's
  representation bytes cannot be read one at a time as `unsigned char`. Real C
  (and PNVI) allows this and expects the copy to preserve provenance. `memcpy`
  covers the common case; a byte-at-a-time copy loop would need a `byte`-level
  read/write pair that keeps the provenance, which is easy to add but not yet
  there.
- `uintptr_to_ptr` takes the intended allocation as a ghost argument instead of
  choosing nondeterministically among the exposed allocations containing the
  address. This is PNVI-ae-udi's "user disambiguation" resolved statically, and
  it is a restriction only for programs that genuinely rely on the ambiguity.
- The effective-type index is defined and carried by layer 0 but not enforced:
  `mem_recall` hands out an unconstrained index. Until that is removed we are
  strictly more permissive than ISO C, in the direction of accepting programs
  clang may miscompile.
- `size_t` is eight bytes and `SizeT.v` is assumed to be below `pow2 64`, for
  the same reason and with the same justification as `Ptr.addr_bound`.
- Palow has no *total* function pointers. Divergence is inferred per body,
  after the wrapper text is built, so every `__fp` wrapper is `divergent` and
  `_total` is not reflected in it. A caller therefore gets `stt_div` where the
  old model would have given `stt`, which is sound but loses the termination
  argument across an indirect call.
- A `_refine` on a `_nullable` parameter is stated as written rather than
  wrapped in `unless_null`. That is a *stronger* precondition than C's -- the
  caller must establish the refinement even when passing NULL -- so it is
  sound, but it is less useful than the old model's phrasing.
- `--palow` translates the user's `_requires`/`_ensures` clauses where it can,
  but all-or-nothing per function: if any clause is untranslatable the whole
  contract is dropped and a `(* contract dropped: ... *)` comment is emitted in
  its place. 107 of 480 contracts are currently dropped this way. A passing
  `make palow-check` therefore says that the translation typechecks, not that
  every function could be implemented against its real contract -- for a
  dropped contract the function has no obligations left to fail.
- `malloc` may return null here, and the old model's allocator cannot: PAL
  emits `Pulse.Lib.C.Ref.alloc_ref`, which always succeeds. So C that
  allocates and then dereferences or frees without testing the result
  translates today and is refused by `--palow`, which accounts for eleven of
  the admitted bodies. This is the deviation being in the honest direction --
  the refused programs have a real bug -- but it is a deviation, and the
  count it costs is real.
- An `if`'s two arms must agree on which locals and `_out` parameters hold a
  value and which still hold uninitialised storage; those are different
  slprops and there is nothing to join them to. This is a real restriction on
  the C we accept rather than an artefact. The `_ensures` a user writes on an
  `if` is ignored, since Pulse infers the join without it.
- The layer-1 points-to predicates are abstract (`CTypes.fsti`,
  `Scalar.fsti`). This is not a matter of taste: a transparent definition
  makes F\* unfold to `encode` when it has to equate two branch-joined values,
  and the proof fails. Byte-level reasoning goes through `t_reveal` and
  `t_conceal`.
- An array parameter's postcondition indexes the *final* sequence, so
  `_ensures(return == *p)` becomes `Seq.index val_p' 0` rather than an
  index into the initial one. That is the right reading for a function that
  may write through `p`, but it differs from PAL today, where `*p` in an
  `_ensures` is resolved against the pointer's current contents in a model
  that does not name the two states separately.
- A translated local always gets a stack slot, even when it is never assigned
  and its address is never taken. An F\* `let` would be cheaper, but choosing
  it needs an analysis whose failure mode is silent, so it is deferred until
  there are measurements to justify it.
- `Etype.ctype` is a closed enumeration covering the types the model uses,
  standing in for what PAL would generate per translation unit. Making it open
  would mean generating `access_ok` per type, which is the same code-generation
  step as every other per-type definition; nothing in the development relies on
  the enumeration being fixed.

## Milestones

1. **Done.** Layer 0: `ptr` with provenance, `bytes`, `mem_pts_to`, split/join/
   disjointness. No translator changes.
2. *In progress; specifications, contracts and straight-line bodies are
   translated.* The
   scalar typed layer is done for the full set of C scalar types (now including
   `size_t`), together with per-type stack alloc/free, `rewrites_to` on reads,
   and `memcpy`. `Pulse.Lib.C.Palow.Examples` fixes the target by hand.

   The translator has a `--palow` mode (`src/pass/emit_palow.rs`) that emits,
   for a whole translation unit, a single `PalowSpecs.fst`: one Pulse `fn` per
   C function, with `ptr` parameters instead of `ref t`, `t_pts_to` instead of
   `Pulse.Lib.Reference.pts_to`, and erased ghost binders for the pointed-to
   values. Bodies are translated for straight-line scalar code -- locals as
   `t_stack_alloc`/`t_stack_free` pairs, dereference as `t_read`, assignment as
   `t_write` -- and everything else gets an `admit()` naming the construct that
   stopped it. `make palow-check` runs this over every test and typechecks the
   result.

   Contracts are translated too. What makes this tractable is that `elab`
   already inserts the explicit `(_specint)` and `(_slprop)` casts that mark
   where a machine value becomes a mathematical one, so the emitter has only to
   follow them. The parameter modes become different ownership shapes rather
   than different types: `_out` starts from `t_pts_to_uninit`, `_const` uses
   `preserves` with a permission binder, `_consumes` appears in the
   precondition only, and a plain parameter gets an existential final value.

   Pointer *extent* is the one thing Palow does not make go away. Every C
   pointer has the same F\* type, which is what removes the pointer-kind
   inference from the translator's type assignment -- but a `T p[]` still owns
   a sequence rather than a single `T`, and that has to be said somewhere. It
   is said in the contract: array parameters get
   `array_pts_to t_repr esize p perm xs` with a `Seq.seq` ghost binder,
   `p._length` becomes `Seq.length xs`, and `*p` becomes `Seq.index xs 0`. The
   distinction moves from the type to the specification; it does not vanish.
   Because `Seq.index` is partial and a postcondition cannot appeal to the
   precondition for its own well-typedness, the emitter collects the bounds it
   needs and conjoins them into the same `pure`.

   Conditionals are translated, and the translator does not have to help.
   Pulse computes the join itself: every Palow points-to predicate carries
   `@@@mkey` on its pointer argument, so the two arms' slprops are matched by
   location and the differing value argument is joined into a `match` on the
   condition. No `ensures` annotation is emitted on an `if` at all, and the
   emitter tracks no values -- the same way `let mut` behaves in ordinary
   Pulse code.

   Getting there required abstracting layer 1. As long as `t_pts_to` was a
   transparent `let`, F\* would unfold it past `mem_pts_to` down to the
   `encode` call and then try to prove two `encode` applications equal, which
   it cannot do for the `match` terms a join produces; with `t_pts_to` an
   abstract `val`, the goal is discharged by congruence on the value argument
   and goes through. `CTypes` and `Scalar` therefore have interfaces now, and
   sizes, alignments and the `t_repr` relations live in the `.fsti` while the
   predicates are opaque. Clients that used to `fold`/`unfold` a scalar
   predicate go through the `t_reveal`/`t_conceal` pair the modules already
   exported for exactly this purpose -- which is also what the design intended:
   the byte-level view is reachable, but only deliberately.

   The one thing the branches do have to agree on is which locals hold a value
   and which still hold uninitialised storage, since those are different
   slprops. That is a real restriction on the C we accept rather than an
   artefact: an `if` that initialises a local on one path only genuinely
   leaves two different states behind. `test/palow_if` is the test for all of this.

   Assertions are translated. `_assert(p)` becomes the loads that `p`
   mentions followed by a Pulse `assert (pure ...)`. This is where the
   deliberate absence of value tracking has to be paid for and turns out to
   cost nothing: a contract has a ghost binder for everything it owns and can
   name a pointee without touching memory, but a body has no such binders, so
   an assertion about `*p` loads `*p` first. A load is the identity on the
   state and its postcondition carries `rewrites_to`, so the proposition Pulse
   ends up checking is exactly the one the C source wrote. Pulse A-normalises
   a call inside `assert (pure ...)`, so most of those loads need no name at
   all, and leaving them in place is better than lifting them: the obligation
   then mentions the contract's own ghost binder rather than a generated
   temporary. An access that also has to open and close a focus does keep its
   name, because the load sits between the two. Both sides of a conjunction
   are loaded, since the loads have to precede the assertion rather than sit
   under it; C's short-circuiting is invisible because an assertion has no
   side effects. `test/palow_assert` covers locals, pointees, an
   assertion following a write, two pointees at once, an ordering through
   `_specint`, and an element of an array parameter.

   Loops are translated. This is the one construct where the translation has
   to ask the C source for something the old model never needed. Pulse infers
   the join for an `if`, but nothing invents a loop invariant, so the emitted
   `invariant` has to restate the *whole* ownership frame: one existential
   binder per live local and per parameter pointee, the points-to that binds
   it, and only then the proposition the C source wrote. A consequence is that
   `_live(x)` carries no information any more and is translated to `True` and
   dropped -- the restated frame already claims the storage, and the old
   model's habit of listing `_live(*p)` in an invariant to keep a pointee
   framed has no analogue here.

   Two syntactic facts about Pulse shaped the output. There is no boolean
   binder on an invariant: `invariant b. ...` parses as a projection and is a
   syntax error, and nothing has to relate the loop's condition to the frame,
   because Pulse re-runs the condition against the invariant and hands its
   truth to the body and its falsity to the exit. And no `decreases` is
   translated -- C has no termination annotation to translate -- so a function
   containing a loop is emitted `divergent`. The loop head keeps the same
   inlining treatment as an assertion, since Pulse A-normalises a call there
   too. `test/palow_loop` covers a loop over locals only, one writing through
   a pointer parameter, and one focusing and unfocusing an array element in
   its body while the invariant holds the whole sequence.

   The refusals in `Body::loop_` are each a real gap rather than caution: a
   loop carrying its own `_requires`/`_ensures`, a loop in a function with an
   `_out` parameter, one over a still-uninitialised slot, one whose condition
   needs a focused access, and one that first initialises a local in its body.
   The body is translated as if it were a branch, so it cannot introduce
   slots.

   A note on how this was validated, because it nearly was not. F\* comments
   *nest*, and quoted C is full of accidental delimiters: `_ensures(*x)` opens
   a nested comment and `(int *)` closes one. `Examples` had been unbalanced
   since it was written, so everything after line 41 -- `swap`, `sum_two`,
   `array_get`, `array_set` -- was a comment, and F\* reported "Verified
   module" for code it had never read. Fixing the comment exposed four real
   errors in the previously dead half. `opt/check-comments.py`, run from `make
   test`, now guards against this class of silent success.

   Allocation is translated, and it is where the payoff of layer 0 shows up
   most directly: `malloc` is an ordinary function with an ordinary
   specification, so the emitter has no `Malloc` case that pattern-matches on
   the AST to guess an allocated type. It emits `malloc t_sizeof`, and the only
   thing about the C type that reaches the model is its size. A custom
   `xmalloc` with the same postcondition would need no translator support at
   all.

   The price is that the specification is *honest about failure*, and that
   turns out to change what C is acceptable. The old model's `alloc_ref` cannot
   return null, so C that ignores the result of `malloc` verifies against it;
   Palow's `malloc` hands the block back under `unless_null`, so the source has
   to test the pointer before it can touch the storage. Three test bodies that
   verified under the old model are now refused with "whose allocation was not
   checked for null", and that is the right answer: those programs have a null
   dereference in them. The `unless_null` elimination has to be spelled out on
   both arms, since a bare `rewrite` cannot see through an `if` decided by a
   pure fact.

   After the check, a block is indistinguishable from a stack allocation --
   `t_claim_uninit` turns the bytes into the same write-only view a
   `t_stack_alloc` hands out -- except for the `freeable` beside it, which is
   what `free` spends. So the store, load and assertion machinery needed no
   changes at all; only the diagnostics did, since a dereference of an
   unchecked block is a different failure from a dereference the contract never
   granted. `calloc` differs only in the byte pattern its postcondition names;
   its zeroing is not yet carried into the claim, so a `calloc`ed block still
   arrives write-only.

   `test/palow_alloc` covers `==`, a bare truth test, `calloc`, reading a block
   back, and allocating a pointer-sized object. The remaining polarity --
   `if (p != NULL) { ... }`, where the *then* arm owns the block -- is
   translated but cannot be an acceptance test, because the old model still
   owns the block on the arm that C takes when the pointer is null and
   therefore leaks there; the emitted shape is in `Examples` instead.

   Globals are translated, and here Palow deliberately changes nothing. The
   design PAL already settled on is about *who owns a global*, and that
   question does not depend on how memory is modelled, so the same three pieces
   come across unchanged: an immutable global -- `const`, or `_pure` -- is
   published as an F\* constant and read with no ownership at all, its address
   is an assumed `ptr`, and the permission that would let something write
   through that address stays under an existential in an assumed `acquire`, so
   no client can ever gather a full one. A mutable global gets the address and
   nothing else; with no points-to ever produced for it, no permission can be
   derived, which is what makes handing the address out inert.

   Assuming the address rather than allocating it is what C says -- a global
   has one fixed address for the whole run -- and it is why `&g == &g` holds
   definitionally rather than needing a lemma. The one thing that had to be
   separated is the address from the value: a struct or array global still has
   an address even though the model has no constant for its contents, so `&g`
   is translated for every addressable global while reads are translated only
   where a value was published. An access *through* a global's address is
   refused, because nothing here owns the storage behind it.

   This was the largest single unblocking so far -- 17 bodies -- mostly because
   a great many test functions mention a constant in passing.
   `test/palow_global` covers assertions over an immutable global, an immutable
   global read as a value, and the pointer identity of a mutable global's
   address.

   `switch` is translated, and it is the one statement where the shape of the
   Pulse output mattered more than the translation. Desugaring a `switch` into
   a chain of `if`s is correct and it verifies, but the cost is not tolerable:
   Pulse infers a join and a frame at every level of the chain, so a
   sixteen-case function nests sixteen deep and ran for over sixteen CPU
   minutes on its own. Emitting a flat Pulse `match` instead brings the whole
   file to twelve seconds. The price of the flat form is that Pulse infers the
   join of an `if` but not of a `match`, so the frame at the join has to be
   written out -- which is exactly the loop-invariant machinery, an `exists*`
   over every live slot with its points-to, plus a `pure` clause. That clause
   comes from the annotation PAL already requires on a `switch`, so no new
   source annotation was introduced; the invariant construction was simply
   factored out and shared between the two.

   Only a `switch` whose cases all end in `break` reaches this code at all --
   fallthrough and a `return` inside a case are desugared into locals and `if`s
   by an earlier pass, and those were already translated. A case listing
   several labels duplicates its body, since Pulse has no or-pattern.

   Functions are now written out in call-graph order rather than source order.
   C only requires a *declaration* before a call, while F\* requires the
   definition, and everything Palow emits lands in one module -- so a body that
   called a function defined further down the file used to be refused for a
   reason that had nothing to do with the memory model. The callee map is built
   from signatures alone, before any body is translated, and the bodies are
   then sorted by what they actually call. Recursion is the one case that
   cannot be sorted away: F\* would want `let rec` and a termination argument
   that C does not supply, so a call that closes a cycle is refused by name and
   the rest of the body is kept.

   `_let` declarations are translated too, and they are the clearest case of
   something the memory model has no opinion about: a `_let` is a name for a
   proposition or a mathematical value that several contracts share, with no
   code and no memory behind it, so the definition Palow emits is the one it
   would emit under any model. It becomes a `GTot` -- or a `Ghost` with the
   `requires`/`ensures` it carries -- and goes into the same table as the
   `_pure` functions, so a contract that mentions one is translated by exactly
   the same path.

   This needed `Spec::value` to learn the boolean connectives. A `_Bool`-valued
   `_let` is *used* as a proposition but has to be *defined* as an F\* `bool`,
   since something will go on to compare it with `true`; the two readings of
   `&&` had to be kept apart. Five bodies came back, all of them functions
   whose overflow obligation was stated with a shared range predicate.

   A batch of scalar gaps was closed at the same time, none of which had
   anything to do with the memory model and all of which were blocking whole
   test files: the shift operators, the conversions between `size_t` and the
   signed types, a pointer used as a truth value, and a negative constant at an
   unsigned type. The last is the only one with a decision in it -- C reduces
   the constant modulo the width, and F\* has no negative unsigned literal to
   write the result with, so the reduction is done in the translator. The
   shifts are gated on the contract having translated, for the same reason
   signed arithmetic is: their width obligation comes from the source's
   `_requires`.

   Two call-site restrictions came off. The first was a bug: a `_plain int32_t
   *` used as a truth value was not recognised as a pointer, because the
   conversion looked through typedefs but not through the annotation wrappers.
   The second was a guess that turned out to be wrong -- passing an array to a
   callee was refused on the theory that the sequence and its permission could
   not be handed over, and in fact Pulse frames the `array_pts_to` and infers
   the permission implicit without help. The refusals a call can still hit are
   now named individually rather than lumped together, which is how the
   remaining ones -- `_out`/`_consumes` parameters, and `_refine`d ones --
   became visible as separate problems.

   A struct local was the last kind of automatic storage with nothing behind
   it. The machine layer got `mem_stack_alloc`/`mem_stack_free`, which hand out
   and take back a flat range of bytes, and everything above that is
   *generated* rather than axiomatised: for each struct Palow emits a
   `stack_alloc` whose body carves the range into the fields with the same
   `mem_split` the scalar layer uses, a `stack_free` that puts it back with
   `mem_join`, a `forget` that drops the values, and a `write_uninit` that
   installs them. This is the payoff the aggregate experiment was for -- there
   is no new axiom for aggregates, only a proof per struct.

   Two things about the carve are worth writing down. It has to run *right to
   left*: `mem_split a n` leaves the prefix at `a` and the suffix at `a +! n`,
   so splitting at descending offsets keeps every suffix pointer literally
   `a +! <absolute offset>`, whereas splitting the other way round nests the
   arithmetic into `((a +! 4) +! 4) +! 1` and the solver does not see through
   it. And the first field is written as plain `a`, not `a +! 0sz`, because a
   `rewrite` will use `add_zero` but slprop matching will not.

   The other half of this was padding. `struct_S_pts_to` was the separating
   conjunction of its fields, which is what makes field access an `unfold`, but
   it left the gaps clang inserts owned by nobody -- so a struct that came out
   of automatic storage could never go back into it, having dropped the gap on
   the way through the points-to. Ownership of a struct now includes a
   `struct_S_padding` conjunct, one existentially quantified byte range per gap
   with only its length pinned, which is also the more faithful reading of C:
   the padding is part of the object. It costs nothing at a field access, since
   it sits in the hole predicate untouched, and it is what makes `forget` and
   `write_uninit` pass storage straight through.

   With storage available, a struct initialiser became worth translating, and
   it is an F\* record literal. A *partial* initialiser is still refused: C
   fills the fields the source leaves out with zero and the emitter has no zero
   to write for an arbitrary field type, so it says so rather than guessing.
   The nineteen "local `X` is struct S" admits are gone; five bodies came back
   immediately and the rest moved on to their next blocker, which is mostly
   that the struct is read or written a field at a time before it has been
   initialised as a whole -- the `init` flag is per slot, and a struct wants it
   per field.

   A field of a *nested* struct came next, which is the same problem wearing
   three different hats: an anonymous member, a first-field cast and an
   explicitly nested struct all arrive as a field access whose base is itself a
   field access. The focus machinery only knew how to reach a base that had an
   address, so it opened one level and stopped. It now recurses: reaching
   `o->in.v` focuses `in` out of `outer` and then `v` out of `in`, and closes
   both in the opposite order. The two orders have to be kept apart, because a
   write through the inner field changes the outer struct's value and a read
   does not, so the outer field closes with the general unfocus in one case and
   the read-only one in the other.

   An assignment used as an expression -- `a = b = v`, or `(y += x)` -- was
   refused only because nothing had written the arm. C says its value is the
   value stored after the conversion to the left operand's type, and
   elaboration has already inserted that conversion, so the emitted store and
   the emitted value are the same term.

   The array-local design went in as designed, and the pleasing part is how
   little of it is new. `maybe_repr` makes an element an `option t` -- `None`
   represents any bytes of the right width -- and `array_pts_to` at that
   representation *is* the predicate for a local array; `array_split`,
   `array_join`, `array_focus` and `array_unfocus` all apply to it unchanged,
   because none of them ever looked at the representation. Allocation is one
   generic proof and needs no unrolling per length: `mem_stack_alloc` gives
   `esize * n` bytes and `Seq.create n None` is what they represent. The two
   wrappers that tie the storage to the array live in a new module, because the
   machine layer sits downstream of the array layer and cannot be opened from
   it.

   A write to `a[i]` focuses the element, drops to the raw bytes, and comes
   back up through the element type's own `_write_uninit` -- the same path a
   scalar local takes -- so the emitter has no notion of an uninitialised
   element to track. A read needs `Some? (Seq.index xs i)`, which is C's rule
   about reading an uninitialised object, and it appears where it belongs: as
   an obligation on the generated code, not as a case the translator refuses.
   The sequence in the proof state is the initialisation state.

   The one asymmetry is that both directions close through `array_unfocus`
   rather than `array_unfocus_read`. What a read puts back is `Some` of what it
   found, which is the same element only up to a proof, and slprop matching is
   syntactic; going through the general unfocus leaves a `Seq.upd` that the
   solver collapses instead.

   A function pointer is a `ptr`. This was a two-line change -- `TypeT::FnPtr`
   joins `TypeT::Pointer` in the two type maps -- and it is the same decision,
   made again, that gave every data pointer a single type: a code address is an
   address, so it gets the address type, and the whole storage layer
   (`ptr_repr`, `ptr_pts_to`, `ptr_read`, `ptr_write`, `ptr_stack_alloc`)
   applies to it without a line of new model. That is the case for collapsing
   the type index in miniature. The existing translator has a `func_ptr a b`
   indexed by the argument and return types, and so would have needed a
   `funcptr_repr` per C function type, an axiom in the machine layer for each,
   and a story for what a cast between two of them means; here there is nothing
   to add, and a cast is the identity because there is only one type to cast
   between. What the *value* means -- which specification the code at that
   address satisfies -- stays where `Pulse.Lib.C.FuncPtr` already puts it, in a
   pure `valid f div pre post` relation that is not about memory at all, and
   that relation is the next piece to port. Thirty function-pointer locals and
   every struct with a function-pointer field stopped being skipped
   immediately, because storing and passing a callback never needed to know its
   spec; only calling through it does.

   A mutable global is owned by the caller. The ownership arrives as a
   `requires` conjunct and leaves as an `ensures` one, at whatever value the
   body left, which makes a global an ordinary slot that happens to have been
   allocated before the program started and is never released -- the storage
   layer needed one new field, an address, and nothing else. The part C does
   not say out loud is *which* globals a function's contract has to name, and
   the answer is not just the ones its body mentions: calling a function that
   touches a global means holding that global at the call, so the sets close
   under the call graph. That is a least fixed point over a finite set, which
   is why recursion is no obstacle.

   One rule fell out of running it. A global that nothing in the file can store
   through is immutable for the whole run whatever its declaration says, and
   handing its ownership around is strictly worse than publishing its value:
   the caller supplies an arbitrary value, so everything the initialiser said
   is lost, and contracts that used to hold stop holding. So a global is owned
   only if some body assigns to it or lets its address escape. The corpus is
   almost entirely of the other kind, which is the honest reason the body count
   barely moved: what this buys is a shape, not coverage. It also cannot be
   acceptance-tested here, because the existing translator refuses to write a
   mutable global at all -- which is rather the point.

   Decaying a named function to a pointer works, and the wrapper is what makes
   it work. `valid` relates an address to a *flat* specification -- `x:a ->
   y:erased c -> stt_div b (pre x y) (post x y)` -- so the arguments become one
   tuple and every binder becomes explicit, and `pre_of`/`post_of` read the
   pre and post back off that type. So the function's contract has to be
   written out a second time, in that shape, as a `func_g__fp` wrapper whose
   body is a single call to `func_g`; `&g` is then
   `of_fn_div (pre_of func_g__fp) (post_of func_g__fp) func_g__fp`, and because
   a function pointer is a `ptr` that value goes into a local, a field or an
   array with no further ceremony. A wrapper is emitted only for a function
   whose address is actually taken.

   Only a function whose parameters carry no ownership gets one so far. A
   pointer parameter's `exists*` is what the witness type `c` exists for, and
   naming the witness is the caller's job at an indirect call; until that is
   translated there is nothing to name it with, so `c` is `unit`. The effect on
   the counts is small and worth being precise about: the fifteen bodies that
   were refused for a function pointer now get as far as the `_ghost_stmt` that
   seeds validity, and are refused for inline Pulse instead. That is real
   progress -- the blocker moved -- but it is progress the histogram records as
   a transfer rather than a gain.

   An indirect call is the other half, and it turns out to be the half that
   makes the first one pay. Where a pointer's target is known -- it was stored
   into the local from a `&g` a moment ago, and the emitter tracks that -- the
   call is `call_div (pre_of func_g__fp) (post_of func_g__fp) addr <tuple>`,
   with `of_fn_div_valid` before it to produce `is_valid` and `drop_is_valid`
   after it to discard it. The address passed is the decay term itself rather
   than a load of the slot. That is the same value, and it keeps `is_valid` and
   the callee syntactically identical, which matters because slprop matching is
   syntactic; going through a load would leave a `pure (f == g)` that nothing
   can discharge.

   The point of doing this is that Palow now establishes for itself exactly the
   facts the existing translator has to be told by hand. In the corpus those
   facts are seeded by a `_ghost_stmt` mentioning `Pulse.Lib.C.FuncPtr`, and
   that ghost statement is inline Pulse, which was blocking the whole body. So
   Palow drops it. Dropping a ghost statement is always sound in the direction
   that matters: a ghost statement is a proof hint, so removing one can never
   make a proof succeed that should have failed, only the reverse. Palow drops
   precisely the hints about the old function-pointer model, because it emits
   the replacements itself, and still refuses every other ghost statement,
   which says something it has no other way to learn.

   Together these are worth thirteen bodies -- the transfer described above,
   reversed and then some. It is not testable in-tree for the same reason the
   written global is not: a `test/palow_*` file has to verify under the
   existing translator too, and that translator needs the `_ghost_stmt` that
   Palow has just made unnecessary. The corpus is the evidence.

   Two smaller gaps fell out of reading the refusals afterwards, both of them
   ordinary work rather than design: an increment or decrement in statement
   position and `memset` were being refused by a catch-all whose message hid
   what it was actually refusing.

   An increment is a read, an add and a write, and the only thing worth saying
   about it is that the old value has to be bound to a name *before* the write,
   because after the write there is nowhere left to read it from. That is also
   exactly what makes `x++` and `++x` differ: both emit the same three steps,
   and they return the bound old value or the new expression respectively. Only
   an integer increment is translated; on a pointer it is pointer arithmetic
   and belongs with that cluster. Worth twelve bodies.

   It also turned up a missing assumption rather than a missing feature.
   `SZ.add` carries a `fits` precondition, `FStar.SizeT.fits` is abstract, and
   Palow had no way to discharge it -- the existing translator gets this from
   `Pulse.Lib.C.Assumptions`, which Palow does not open. Since `CTypes` already
   assumes an LP64 `size_t` twice over, for `size_t_bound` and for the
   conversions, the honest place for it is beside them: `size_t_fits`, with an
   `SMTPat`, so a `size_t` addition whose bound the source has established does
   not need a hint at every use.

   `memset` came next, and it splits cleanly in two. Zeroing a whole object
   raises the padding question this document has already asked once: a
   structure write sets the field bytes, but `memset` sets the padding too, so
   the two are not the same operation at the byte level. It turns out not to
   matter, and for a reason worth recording. Padding is already its own slprop,
   `struct_S_padding a p`, which says the bytes are owned and says nothing
   about their contents; both operations leave that untouched. So translating
   the `memset` as a write of the type's zero value forgets that the padding
   became zero, and forgetting is the safe direction -- the result is a weaker
   postcondition, not a wrong one.

   That needed a `struct_S_write` beside the existing `struct_S_write_uninit`,
   which is `struct_S_forget` followed by the uninitialised write. Composing
   the two rather than writing the fields in place is not a detour: both need
   the full permission anyway, and it keeps the padding handled in one place
   instead of two. The zero value itself is built structurally, and two types
   are deliberately absent from it. A pointer is absent because an all-zero
   pointer is the null pointer only on a target that says so, and the byte
   layer has no such assumption. A union is absent for a better reason: zeroing
   it is a statement about bytes, and which value that names depends on which
   member is read afterwards.

   The other half -- `memset(a, 0, n * sizeof(T))` over an array -- wants a
   fill in the array layer, which does not exist yet, and a structure with an
   array field is refused for the same reason. That is ordinary work and is
   left for next.

   Publishing an array global was worth more, and it is the same idea as the
   immutable scalar global one layer up. `_pure const char padded[16] =
   "packets";` cannot be written by anything, so it does not need to be an
   object at all: it is published as a sequence constant, and `padded[0]` is
   `Seq.index var_padded 0` -- a term, with no ownership, no focus and no
   sequencing, which is also what lets it appear inside an assertion. The
   initialiser arrives already padded out to the declared length, so the value
   is a `Seq.create` with one `Seq.upd` per element that is not zero.

   How the value is written down turned out to matter more than anything else
   here. The first attempt was a `Seq.create` with one `Seq.upd` per element,
   and it does not scale: checking that against a length refinement costs a
   subtyping step per element, and the corpus' thousand-element table took a
   test run from fifteen minutes to over half an hour without finishing. A flat
   list fixes it, exactly as `array_spec_of_list` does in the existing model.
   The value is one application, and the length comes out of `normalize_term`
   in an implicit rather than from the solver. `const_seq` is abstract, and
   that part is load-bearing: left transparent it is `Seq.seq_of_list`, which
   is recursive, and the solver unfolds it instead of using the indexing lemma
   -- which works for the first few elements and then quietly stops.

   Indexing is settled more directly still. A constant index into a constant
   table is just the element, so that is what is emitted: nothing can write the
   global, so the value is known at translation time, and the solver never has
   to walk the list at all. The thousand-element table now verifies in three
   and a half seconds. Reducing a symbolic index needs the list lemmas, and
   those work in isolation but are crowded out by the generated file's other
   patterns -- which does not bite yet, because a symbolic index needs a
   `_requires` to be in bounds and the one case in the corpus has none.

   Two limits, then, and neither is arbitrary. The length is in the type, so a
   constant subscript carries its own bound; a computed one still needs the
   function's `_requires`, and without one it is refused rather than emitted to
   fail. And `_pulse_opaque_to_smt` on the declaration is honoured, hiding the
   value from SMT while leaving the length visible.

   The same reasoning generalises past arrays. Any path into an immutable
   global -- a field, an element, a field of an element -- reads a value that
   nothing in the program can change, so it is settled at translation time and
   needs no ownership, no focus and no sequencing. Palow now walks such a path
   through the initialiser and emits the constant it arrives at, which is also
   what lets it appear inside an `_assert`. A path the initialiser does not
   mention is not a gap but the zero-fill C guarantees for the rest of a
   partial initialiser, so that is what is emitted. Only scalars fold; an
   aggregate path falls back to the ordinary read.

   A local pointer set once to the address of a place is the other case where
   nothing needs to be modelled. `int32_t *q = &p->first; *q = v;` -- which is
   what a first-field cast comes out as -- gives `q` no storage in C either,
   and modelling it as an object would mean holding a focus on `p->first` open
   from the declaration to the last use, with arbitrary statements in between.
   Substituting the place at each use avoids the question and is what the C
   means. It is only the same C if the place denotes the same object
   throughout, so the alias is taken only when nothing rebinds the pointer
   again and nothing rebinds any name the place is built from; writing
   *through* those names is fine, and is the point. Handing the pointer itself
   to something else is still refused, because that hands out ownership of the
   place, which is the focus-across-statements problem again.

   Pointer arithmetic is where the low-level model is *simpler* than the one
   it replaces. `p + 3` is `p +! 3 * sizeof elem`, `p < q` compares addresses,
   and `p - q` is a byte difference divided by the element size -- exactly the
   identity C states, and nothing has to be tracked to say it. The old model
   carried a separate `_arrayptr` pointer kind whose comparison and difference
   needed a `base_of x == base_of z` precondition, because a pointer there was
   an array plus an offset and there was no other way to say two of them were
   comparable. Here they are addresses, so they always are. ISO C disagrees:
   `<`, `<=` and `-` are defined only within a single object (C11 6.5.6p9,
   6.5.8p5), and forming an out-of-bounds pointer is undefined even if it is
   never dereferenced. Palow is more permissive on both counts, which is the
   same deviation `( +! )` already had -- forming a pointer is not an access,
   and it is the access the ownership discipline governs.

   With arithmetic in place the ghost hints that went with it can go. Palow
   already dropped the hints about the old function-pointer model because it
   emits the replacements itself; the same is now true of the array-cell borrow
   discipline, the maybe-uninitialised discipline, and acquiring a global's
   storage. None of those exist here: an array access is a focus the emitter
   writes, initialisation state is `write_uninit` and `forget`, and a global's
   ownership arrives in the contract. Dropping a hint is sound in one direction
   only, and it is the safe one -- a hint can make a proof succeed that would
   otherwise fail, so removing one can only cause a failure. Every other ghost
   statement is still refused rather than silently discarded.

   `ptrdiff_t` gets no layer of its own: on the LP64 target Palow fixes, it
   *is* `int64_t`, so it shares its storage.

   Reading a global through its address is the case that makes the alias pay
   for itself. `const uint32_t *p = &g; return *p;` is what most of the corpus
   writes, and it was the single largest remaining refusal once pointer
   arithmetic landed. The alias turns `*p` back into `g`, which is a published
   constant, so nothing is owned and nothing is read. Allowing a bare variable
   as the aliased place needed one correction elsewhere: taking a name's
   address normally counts as a write, since something may store through it,
   but an address that goes to an alias does not escape. Each accepted alias
   therefore pays back the write its own `&` charged -- and, since an alias
   that is *rejected* did let the address escape after all, that discount has
   to be withdrawn and the rest reconsidered, which is why the analysis is a
   fixpoint rather than one pass. The effect on the model is direct: globals
   that looked mutable only because their address was taken are immutable
   again, and go back to being constants.

   A global with no initialiser is not a gap either. A tentative definition is
   initialised as if by zero (C17 6.9.2p2), so its value is as settled as an
   explicit one. That zero is *not* the `memset` zero: C11 6.7.9p10 says an
   arithmetic member starts at zero and a pointer member starts at a null
   pointer, which is a statement about values rather than about bytes, so
   unlike the `memset` case it has an answer for a pointer and that answer is
   `null` on every target.

   `extern const T g;` stays refused. It is immutable, but which value it is
   was decided in another translation unit, and Palow emits one module per unit
   with nowhere to put the shared constant. The old model links them with a
   generated per-global module; doing the same here is a known gap.

   A `_refine` on a parameter is a conjunct of that parameter's points-to, so
   the place to put it is wherever that points-to is stated: on entry, where
   the caller supplies the ownership, and on exit, where the callee hands it
   back. Which of the two apply is decided by the parameter mode and not by the
   refinement -- an `_out` parameter has no incoming value, so only the exit
   side fires; a `_consumes` parameter is never handed back, so only the entry
   side does. The pointee map that already drives contract translation records
   exactly that distinction, one term per side with `None` where there is no
   value, so the rule reads straight off it.

   Translating the clause needs no substitution. `this` is bound in the pointee
   map to the same pair of terms as the parameter it refines, and `*this` then
   resolves through the map like any other dereference. What it does need is a
   type: the clause is never elaborated, because `this` is free in it and
   nothing could have typed it, so `this` is also bound in a copy of the
   environment to the parameter's own type -- which is not a workaround but the
   definition of what `this` is.

   Until now the refinement was simply dropped and every *caller* refused, on
   the grounds that a caller which could not see the refinement would be
   proving against a specification weaker than the source's. That reasoning was
   right, and it is why the refusal now keys off whether the contract
   translated rather than off the presence of a `_refine` at all. Two kinds
   stay untranslated: `_refine_uninit`, which talks about a points-to that has
   no value here, and `_refine_value`, which binds a name the contract
   machinery does not carry. Neither drops the function -- the contract is
   marked dropped, which is what already stops a caller from trusting it.

   Which function an indirect call reaches is the one thing about a pointer
   that no points-to can say. `is_valid` relates an *address* to what the code
   there does, and the bytes of a code pointer say only where the code is, so
   an indirect call translates exactly when the emitter can name the target.
   It could previously do that only for a local slot it had watched being set.
   Three more ways of knowing were missing, and each is the same observation
   from a different angle.

   The first is that a copy carries the target with it: `fp2 = fp1` makes
   `fp2` reach whatever `fp1` reached. The rule that was there did not
   propagate, and -- more importantly -- did not *clear*, so a slot reassigned
   from something unknown kept its old note. Resolving the right-hand side
   with the same function that resolves a call site fixes both at once, and
   the clearing half is the one that matters, because keeping a stale note is
   the only way this could go wrong.

   The second is that the address is often not in a slot at all but written
   down in something immutable, which is the interesting case: a dispatch
   table is a constant, and the point of a constant one is that nothing ever
   stores into it. That is a constant path into an immutable global, which
   Palow already reads for any other type, so a call through `g_ops.op`
   resolves the same way `g_ops.n` does. A union member is included, but only
   the one the initialiser named: the bytes of the others are there, and what
   they mean at another type is a reinterpretation the initialiser did not
   decide.

   The third is that a wrapper has to exist for what those initialisers name.
   The decay analysis scanned function bodies only, so a table whose entries
   are mentioned nowhere else got a call to a wrapper that was never emitted.

   Two contract gaps were holding wrappers back for an unrelated reason, since
   a wrapper reflects the contract and so is refused when the contract is. A
   negation is a subtraction from zero, so it is undefined on overflow for the
   same reason and reads mathematically for the same reason; and an integer
   conversion in a contract is the conversion the body would emit, there being
   no reason for a contract to describe a narrowing differently from the code
   it constrains.

   What is left in this cluster is genuinely harder and splits cleanly. A
   callback parameter carries its target's contract in a `_refine`, which now
   reaches the emitted specification -- but the ones in the corpus are written
   as inline Pulse against the old model's module names, so they move with the
   inline-Pulse work rather than before it. A field of a *local* struct needs
   the note to be kept per path rather than per slot. And a function with a
   pointer parameter still has no wrapper at all: the witness type `c` in
   `valid` is `unit`, and threading a real one needs the caller to name the
   witness at the call.

   Three small things then finished the constant-global story, and all three
   are cases where the general rule was already right and only its reach was
   short. Reading a global *through its address* -- `const struct point *p =
   &g; return p->y;` -- is how C code normally gets at one, and the constant
   path did not follow the alias, so it saw a dereference of a pointer instead
   of a field of `g`. What an initialiser did not reach was being filled with
   the `memset` zero rather than the static one, which has no answer for a
   pointer: C11 6.7.9p10 says the member is a *null pointer*, and saying so is
   what lets `if (g.callback == 0)` translate. And an array the initialiser
   never reached is zero at every index, so the subscript need not be a
   constant -- the only case where a symbolic index reads as a value, and the
   common one, since a static aggregate with no initialiser is exactly that.

   An `_out` argument is the one place where a call is handed a place rather
   than a value, so it is the one argument that is not evaluated: `&x` is
   storage. What the callee asks for is the write-only points-to, and the two
   things that can supply one -- a local that has not been written, and the
   caller's own `_out` parameter -- are both already tracked, because the
   emitter needs them to choose between an initialising and an ordinary store.
   So the call site does nothing new: it spends one and records that it is now
   initialised.

   The interesting case is passing storage that *has* been written, which C
   allows: `_out` says the callee writes the object, not that nobody wrote it
   before. There the value has to be given up first, which is the same step a
   local takes on its way to `_stack_free` and is a loss of knowledge rather
   than of ownership. `_consumes` at a call site is still refused, because
   ownership that does not come back is not something the caller's slot
   bookkeeping can currently spend.

   Everything above went into a single `PalowSpecs.fst` per translation unit,
   which was the right shape while the question was only whether the model
   typechecks. It is the wrong shape for a translator. A helper a user writes
   by hand has to be able to sit *between* two generated declarations --
   naming the first and being named by the second -- and a single module
   leaves nowhere for it to go; that is exactly why every `_include_pulse` is
   still untranslated, and it is the same reason an `extern` global cannot be
   linked to the translation unit that defines it. So Palow now emits one
   module per declaration, named as the old translator names them:
   `Struct_s`, `Global_g`, `Let_l`, `Func_f`.

   The split needed no reordering. The single-module output typechecked, and
   F\* requires a definition to precede its use within a module, so the order
   the chunks were already produced in *is* a valid definition order. All that
   is left to decide is which earlier modules each one opens, and that is read
   off the generated text: a chunk's top-level names are the identifiers at
   column zero after the modifier keywords, and a chunk opens every earlier
   module one of whose names it mentions. The edges only ever point backwards,
   so the graph cannot have a cycle -- which is not a detail, because F\*
   modules may not be mutually recursive while C declarations routinely refer
   to each other in an order the file does not fix.

   Reading dependencies out of generated text would be unforgivable for a
   general F\* input and is safe here for one reason: the text is generated.
   Every definition starts at column zero and every continuation line is
   indented, which the emitter maintains regardless because Pulse is
   indentation-sensitive. A false edge would only cost a redundant `open`; a
   missed one fails loudly at F\*.

   The output directory now also carries `TranslationErrors.fst` and
   `diagnostics.json`, so an IDE pointed at it finds what it finds for the old
   translator. `source_range_info.json` does not exist yet, because Palow
   emits strings rather than `pretty` documents and so has no source ranges to
   report.

   This also corrects a measurement. Before the split, `issue51_test` took
   1.2s under Palow against 1m30 under the old translator, which looked like a
   thirtyfold win and was mostly an artefact: the old side paid F\* startup 139
   times and Palow paid it once. One module per declaration now costs Palow 35
   seconds for the same 60 functions. The remaining 2.5x is real, but it is a
   quarter of what the single-file number suggested, and anyone quoting the
   old figure should stop.

   **Unions are the first generated type with a byte-level representation.**
   A generated struct still has none: its points-to is the conjunction of its
   fields', which says nothing about the padding between them, and that is
   enough for most uses. A union has no such conjunction to write, because its
   members overlap by definition, so `union_X_pts_to` has to go through
   `mem_pts_to` and a `union_X_repr` over the bytes. That is more work, and it
   pays for itself: having a byte-level representation is exactly the
   condition for being an array element or a member of another union, so a
   union can already be both where a generated struct cannot.

   `union_X_repr` is deliberately not injective. The bytes that encode one
   member also encode whatever the other members would read them as -- that
   *is* type punning, which is the reason C programs use unions -- so there is
   nothing to be injective about. Palow never relies on injectivity anywhere.

   The asymmetry between `union_X_focus_m` and `union_X_switch_m` carries the
   C rule. Focus needs to know that `m` is the member the value is tagged
   with, and hands out that member's value. Switch cannot know it -- the union
   may hold anything -- so it hands out uninitialised *storage*, and needs
   full permission for the same reason a write does. Reading a member is
   therefore translatable exactly when a write to that member came first,
   which is C's rule stated as a proof obligation rather than as prose. A
   write needs no such history and is never refused.

   The emitter tracks which member is live per address, and gives that
   knowledge up the moment control leaves: at a call, at either arm of an
   `if`, at a `switch`, around a loop, and at a whole-union write. Over-
   clearing costs an `admit()`; under-clearing would emit a read F\* rejects,
   so the bias is the safe one.

   Two smaller decisions. Every member gets a `union_X_rest_m` predicate for
   the bytes past it, including a full-width member whose rest has length
   zero: `mem_split` returns a suffix either way, a resource cannot be
   dropped, and telling the two cases apart is longer than not doing so. And a
   whole-union write matches on the *value*, not on memory, because nothing
   reads a tag that C does not store.

   **A struct gets a byte-level representation too, up to a size.** The
   earlier claim that a generated struct cannot have one was too strong: it
   was the *definition* of ownership that was field-wise, not the object. A
   struct now carries both views. `struct_X_pts_to` stays the conjunction of
   its fields' points-to, which is what a field access needs and what lets two
   fields hold different fractional permissions; `struct_X_repr` relates a
   value to the object's bytes, which is what an array element or a union
   member has to be. Neither is defined from the other. They are related by a
   generated proof, `struct_X_reveal` and `struct_X_conceal`.

   That proof is a partition argument run in both directions, and the
   directions are not symmetric. `_reveal` reveals each field's bytes and
   joins the pieces left to right; `_conceal` splits the object right to left
   and conceals each piece back into its field. Both orders are forced: joining
   right to left, or splitting left to right, nests the address arithmetic into
   `((a +! 4) +! 4) +! 1`, and the solver does not see through that. Going the
   other way every intermediate address stays `a +! <absolute offset>`. The
   automatic-storage carve had already discovered the splitting half of this;
   the joining half is its mirror.

   The representation pins the fields and says nothing about the padding, which
   is what C guarantees: the gaps hold unspecified values and two objects with
   equal fields may differ there. Ownership of the gaps is still part of the
   struct -- it always was, in `struct_X_padding` -- because an object that
   lost them on the way through `_pts_to` could never go back into storage.

   There is a size limit, and it is about the proof rather than the model.
   `_reveal` has to recognise each field's slice of the finished object
   through the appends stacked above it, which is one lemma call per field per
   region above it. For the handful of fields a struct used as an array
   element or a union member actually has, that is nothing. For the
   two-hundred-field configuration records that appear in real headers --
   `_profile_descriptor_t` in the DPE test is one -- it is forty thousand, and
   F\* will not finish. Those keep the field-wise view, which is linear, and
   which is the only one they are ever used through. The cutoff is sixteen
   fields.

   Four things fell out of having it. A struct can be an array element, so
   `struct point pts[]` is a contract rather than a skip. A struct can be a
   union member, which is what `test/dpe`'s `_u_context_t` needed. A struct can
   be claimed from raw storage without that storage having come from a stack
   allocation, because `_claim_uninit` is now separate from `_stack_alloc`. And
   a struct can be read as a whole value, which a by-value parameter needs --
   except when it contains a union, which has no `_read` and never will,
   because reading one would mean branching on a ghost tag inside a real
   function.

   Two smaller fixes came with it. A common-initial-sequence union that PAL
   collapses into a struct was losing its layout: the table is keyed by how a
   type is spelled, and nothing moved the entry from the union key to the
   struct key, so every struct containing one was skipped for having a field
   of unknown size. And a struct carrying a `_refine` passed *by value* now
   reports a dropped contract instead of producing a body that cannot be
   proved -- the refinement is not part of the generated `_pts_to` yet, which
   costs nothing behind a pointer and is the whole contract for a value.

   **Brace initialisers.** Once a struct is a record and a union is a tagged
   value, `struct point p = { .x = 1, .y = 2 }` needs no writes at all: it is
   an F\* record literal, and `union foo f = { .x = 67 }` is `Union_foo_x 67l`.
   The earlier emitter refused a *partial* initialiser rather than guess at the
   missing fields, which was the right caution but not necessary: C says the
   fields you leave out are zeroed, and `zero_value` already builds the zero of
   any translatable type, recursively through nested structs and arrays. So a
   partial initialiser is now a full translation rather than a skip.

   A union initialiser also carries the one piece of information a union write
   has to record. The member it names is the member it makes live, and the
   emitter can read that off the source expression instead of trying to recover
   it from a value it has just erased -- so initialising a union and then
   reading the member back now works, which is the shape most union code in the
   test suite starts with.

   **Hand-written Pulse is spliced in as written.** `_ghost_stmt`,
   `_inline_pulse` and `_include_pulse` are escape hatches: the text is the
   author's, so the only thing to translate is the antiquotations, which are
   exactly the places where a fragment has to name something only the emitter
   knows. `$(e)` becomes whatever the C value `e` reads as, `$&(e)` its
   address, `$type` and `$field` the generated names. An `_include_pulse` block
   becomes a module of its own, ahead of everything that may name it, with its
   `open`s computed the same way as any other module's.

   `$unfold` and its relatives are the exception, and are refused rather than
   guessed at: they name helpers the old emitter generated around its own
   representation of a struct, and Palow's representation is a different thing,
   so there is nothing honest to point them at.

   This is where the two models stop being interchangeable at the source level.
   A fragment names the predicates of whichever model it was written for, and
   Palow's are not the old model's -- `int32_t_pts_to a 1.0R x` where the old
   model writes `a |-> x`. The decision was to let Palow's vocabulary be the
   default and to port the fragments; a test whose annotations then no longer
   make sense to the old translator carries a `palow-only` marker and is
   compiled but not translated by it. Eleven tests whose fragments are
   substantial proofs against the old model -- `container_of`, `core_ref`,
   arrayptr and nullable idioms, `dpe`, `func_pointer` -- carry the opposite
   marker, `palow-old-annotations`, and Palow drops their fragments for now.
   That marker is a backlog rather than a design: it names exactly the
   annotations still to be ported, and the count is meant to go to zero.

   **`_nullable` says the ownership is conditional.** A nullable pointer may be
   null, so what the contract owns is not the pointee but `unless_null p (...)`
   -- the ownership, unless there is nothing to own. Until now Palow dropped it
   entirely and emitted `requires emp`, and did so *silently*, which is worse
   than the gap itself: the whole measurement rests on every weakening being
   counted, and this one was not. It is now the guarded points-to, in all four
   parameter modes, with the erased value binder kept -- when the pointer is
   null the binder is simply arbitrary, which is exactly how the guard gets
   introduced.

   What the guard does *not* do is put the pointee back in scope. A contract
   that mentions `*p`, or a body that reads it, is talking about something the
   caller has not unconditionally granted, so a nullable parameter stays out of
   the pointee map and those cases report a dropped contract rather than
   quietly proving against a precondition nobody supplied. A refinement behind
   the guard is reported for the same reason: the refinement is a pure fact and
   the guard is an slprop, so there is no honest place to put it yet.

   Fixing this exposed a second thing worth recording. The exit ownership was
   being built by appending the existential binder to a points-to with its last
   argument left off, which works only while the value is the last thing in the
   term. Inside `unless_null` it is not, and the emitted postcondition came out
   with the binder outside the guard. The binder is now substituted where it
   belongs, which is what it should always have been.

   Inline Pulse in a *contract* was the largest single cluster of dropped
   clauses -- 35 of the 91 -- and it is now spliced in as written, on the same
   terms as a ghost statement. A clause whose type is `_slprop` is ownership,
   not a proposition, so it goes into `requires`/`ensures` directly rather than
   under `pure`; the rest keep their `pure` wrapper. Both kinds are subject to
   the usual rule that a clause which cannot be translated takes the whole
   contract down with it, so a partially-understood specification is never
   proved. `_assert` of a hand-written slprop follows the same split, and its
   antiquotations are folded into the term rather than lifted into preceding
   statements -- a fragment is a single term, and a call spliced out of one
   would run.

   Two smaller things fell out of this. A fragment written across several lines
   was being dropped into a `requires` at column zero, which Pulse reads as the
   end of the clause, so a fragment is now flattened to one line (and one
   carrying a line comment is refused rather than mangled). And ghost
   statements following a `return` are no longer discarded: the returned value
   is bound to a name, `$(return)` resolves to it, and the statements run
   before the frame is released. That is the only way to establish a
   postcondition that talks about the result, and it is what `return_ghost`
   exists to test -- that test now verifies with no admits at all.

   The honest accounting is that the *dropped-contract* count went up, from 91
   to 99, because ten more tests were marked `palow-old-annotations`. Their
   fragments name things the old model has and this one does not -- `core_to_ref`,
   `arrayptr_pts_to`, the generated `__aux_raw_unfolded` helpers, `|->`, even
   the old emitter's mangled `return_1`. Before contract splicing existed those
   clauses were dropped anyway and the marker was unnecessary; now that
   splicing works, refusing them explicitly is what keeps the number meaning
   what it says.

   A second silent weakening turned up while doing this, with the same shape as
   the `_nullable` one: a `_plain` parameter carrying a `_refine_value` was
   skipped by an early-out that ran before the refinement check, so a
   user-supplied ownership predicate vanished without a note. The check now
   runs first. Both holes were found by reading the code rather than by any
   test failing, which suggests the remaining early-outs in the parameter loop
   deserve the same audit.

   Auditing the rest of the parameter loop for the same pattern turned up one
   more, though this one no test exercises yet. `_live(x)` was translating to
   `True` unconditionally, on the reasoning that the frame has already claimed
   the storage -- true for an owned parameter and for a local a loop invariant
   binds, and the reason `_live` clauses are dropped from invariants rather
   than conjoined. It is not true for a `_nullable` parameter, whose storage is
   exactly what the guard withholds: there, `_live(p)` *is* the claim that the
   guard is discharged, and answering `True` would grant it for free. Those
   parameters are now tracked separately and `_live` on one reports instead.
   The first attempt at this was stricter -- report unless the name is in the
   pointee map or the invariant's local bindings -- and it cost eight bodies,
   because a by-value scalar parameter is in neither map and is trivially live
   all the same. Being exactly as strict as the model requires, and no
   stricter, is the whole discipline in miniature.

   One structural prerequisite for underpinning `emit` turned out to be nearly
   free. The two emitters already write the same layout -- one flat output
   directory, one file per module, plus `TranslationErrors.fst` and
   `diagnostics.json` -- but Palow wrote no `source_range_info.json`, which is
   what an IDE uses to get from a generated file back to the code that made it.
   The old emitter builds that from a token-level range map its pretty-printer
   maintains; Palow has no such map and building one would mean rewriting every
   `format!` in the emitter. It does not need one. One module per declaration
   means the declaration's own range is the answer for the whole file, so each
   chunk now carries the source file, range and C name of the declaration it
   came from, and the document is emitted with an empty `mappings` list. That
   is navigation at declaration granularity rather than at token granularity,
   and an empty list is the honest way to say so: a wrong position inside a
   module would be worse than none.

   Splitting the marker was the next thing, because the count it feeds was
   quietly dishonest. `palow-old-annotations` is a backlog and is meant to
   reach zero. But four of the twenty tests carrying it exist *to* exercise
   what the old model has and this one deliberately does not: `antiquot` is a
   test of the `$fold`/`$unfold` antiquotations, which name generated struct
   helpers Palow has no counterpart for, and `core_ref_use`, `core_ref_struct`
   and `packet_space_connection` are tests of `_core_ref`, a concept this model
   removes outright. Those now carry `palow-model-specific` instead, and the
   note in the generated file says which kind it is, so a census separates
   them: **21 admits from the backlog and 6 from the floor**. Counting the two
   together would have made a permanent floor look like unfinished work.

   The split immediately paid for itself by exposing something neither bucket
   covered. `_allocated` is not a user annotation at all -- it is PAL's own
   macro, and it expands to a refinement whose predicate is an `_slprop`:
   `_refine((_slprop) _inline_pulse(freeable $(this)))`. A refinement that is
   ownership rather than a fact about a value had nowhere to go, so it fell
   through to the proposition translator and took five contracts down with it.
   Such refinements now go where the points-to goes, at whichever ends of the
   contract the parameter's ownership is stated.

   The fragment itself needed one more decision. This model's `freeable`
   carries the size of the block, because the right to free something is
   meaningless without saying how much, and a nullary macro has nowhere to put
   a `sizeof`. Rather than change `pal.h` -- shared with the old emitter, whose
   `freeable` takes one argument -- Palow recognises the shape `_allocated`
   expands to and rebuilds the term with the pointee's size, which is exactly
   what `_allocated` on a `T *` typedef means. Any *other* `_slprop` refinement
   is hand-written and is spliced as written. `sum_point` now verifies with
   `freeable var_p 8sz` in both directions.

   Quantifiers in contracts came next, and were the largest cluster left that
   needed no model work at all: `_forall` and `_exists` were simply absent from
   the proposition translator, which cost eight contracts across
   `compare_elements`, `implies`, `rec_fn`, `recursive_functions`,
   `reverse_test` and `with_pure_quantifier` -- every specification that says
   something about a whole array rather than about one element. The bound
   variable is bound at its C type, not at `nat`: `_forall(size_t i, ...)` is a
   claim about every `size_t`, and binding it that way is what lets every other
   translation path -- `a[i]`, `i < len` -- work unchanged underneath.

   The one real decision was where the partiality side conditions go. `Seq.index`
   is total only in range, and this emitter already collects the bounds
   obligations an indexing contract raises and conjoins them to the clause. A
   bound raised *inside* a quantifier must stay inside it: hoisting it out would
   be ill-typed, since the fact that makes the access total is usually the
   quantifier's own antecedent. So a quantified body is translated in a nested
   scope with its own obligation list, and the result is `forall x. G ==> p`
   (or `exists x. G /\ p`). That is weaker than `forall x. p`, and deliberately
   so: for an out-of-range `i`, `a[i]` is undefined in C, so "whenever the
   access is defined" is the faithful reading rather than a concession.

   Quantifiers inside an `_assert` needed a second, narrower answer. An
   assertion in a body translates by *emitting* the loads its operands need,
   and a load underneath a binder would have to run once per witness -- there
   is no such thing. A quantified assertion is therefore translated only when
   its body turns out to need no memory at all, and rather than predict that,
   the emitter translates the body and then checks whether anything was
   emitted, discarding it if so. That covers the pure quantifiers
   `with_pure_quantifier` exists to test and reports honestly on the rest.

   Naming a constant in a contract came next: `_forall` had made array
   contracts translatable, and the names a contract most often wants after an
   array are the ones C already treats as constants. Three shapes were dropped
   whole. An enumerator has no storage at all, so its value is the only thing
   there is to say about it and it is now inlined where it appears. A `const`
   this file initialises is already published by its own module as an F\*
   `let`, so a contract can simply name it.

   The third shape needed a decision rather than a lookup. `extern const T g;`
   is immutable, but which value it is was decided in another translation unit,
   and this emitter used to refuse it -- the reasoning being that there was
   nowhere to put a constant shared between units. One module per declaration
   has since made that false: `Global_g` is exactly that place, so an `extern`
   `const` is now published as `assume val var_g : T`, abstract but fixed. A
   reader learns that every read yields *the same* value, which is the whole
   content of `const` at an unknown initialiser, and that is enough for
   `_ensures(return == g)`. Reading one needs no ownership, for the same reason
   reading a known constant does not: nothing in the program can write it, so
   there is no moment at which the read happens.

   Making a contract name a global also exposed a gap in how modules are
   opened. A module's `open`s were derived from what its *body* uses, which is
   silently wrong whenever the body is admitted and the contract is not -- and
   that is now a common case rather than a corner. Contracts collect their own
   uses and both sets are unioned.

   The same work showed that the coverage harness had been reading the suite
   one file at a time, while the per-test Makefile hands PAL every file at
   once. A file is not a translation unit to PAL: it combines them, and
   `extern_globals` depends on exactly that, stating a contract about a `const`
   whose value is written down in a sibling file. Read apart, the two halves
   can only say that the value is fixed, not which one it is. The harness now
   translates each test in one invocation, which is both the honest scope and a
   slightly smaller one, since a function declared in a shared header used to
   be counted once per file that saw it.

   The last thing a contract can name that this emitter had no answer for was a
   word the *author* coined. Three annotations exist for that -- `_type` names
   an F\* type, a `_let` returning `_slprop` names a piece of ownership, and
   `_ghost_arg` adds a value that exists only so the contract can talk about it
   -- and none of them is the memory model's business. A `_type` never
   describes storage; an slprop-valued `_let` is hand-written Pulse by
   construction, since the model has no other way to spell one; a `_ghost_arg`
   has no representation at all, which is precisely what an erased implicit is.
   So all three are passed through, and `ghost_arg`'s `tank_owns(t, n)` now
   reads in `requires` and `ensures` exactly as it does in the old translator's
   output. A call to an slprop-valued `_let` is routed to the ownership side of
   the contract by the same split `_allocated` uses: the author gave a piece of
   ownership a word, and a contract that uses the word means the ownership.

   An allocation of an *array* is now translated. The model needs nothing new
   for it: `malloc` and `calloc` take a byte count, so `T *a = malloc(n *
   sizeof(T))` is a sized allocation followed by a claim that the range is an
   array of `T`, and after the claim the state is exactly what a fixed local
   array already leaves behind. The only genuinely new obligation is `calloc`'s
   promise that the storage arrives readable: that needs an all-zero range to
   *be* the encoding of the value zero, which is now a lemma (`encode_zero`)
   and is named explicitly at the claim, since the fact is wanted at `encode 4
   None (I32.v 0l)` and an `SMTPat` keyed on a literal `0` would not fire
   there. Overflow in `n * sizeof(T)` is the translator's problem, not the
   model's: a literal count is folded at translation time, and a variable count
   emits a `size_t` multiplication and is reported unless a translated
   `_requires` is there to discharge it.

   This gained almost no bodies on the existing suite, and the reason is worth
   recording: not one existing test checks the result of an array allocation
   against null. They all land instead on the pre-existing, honest refusal to
   dereference storage whose allocation was never checked -- so the cluster
   "an allocation is not translated yet" fell from ten to five, but five of
   those simply moved one wall further along. `test/array_alloc` exists to
   exercise the feature properly, with four functions that do check: a `malloc`
   written then read, a `calloc` read *before* it is written, a `calloc`
   written over its zeros, and `_length` of a heap array. All four verify with
   no admits.

   A sixth silent weakening turned up, and this one had been there from the
   beginning: a `_refine` on a parameter that is not a pointer was dropped
   without a word. Refinements were collected only while walking a parameter's
   *pointee*, so a parameter with no pointee -- a scalar, a function pointer --
   never reached the collection at all. Every callback parameter in
   `func_pointer` was in that position: its `_refine` supplies the `is_valid`
   fact the indirect call needs, and the emitted contract simply did not have
   it. Nine contracts across the suite were weaker than they looked.

   The fix has two halves. A refinement now says which of the two things it is
   by where `this` can be bound. For a pointer, `this` inherits the pointee
   entry and `$(this)` reads through it, as before. For anything else there is
   no storage, so `this` is bound as a local standing for the value, at the
   *peeled* type -- leaving the refinement on would make the binder's type the
   very thing being refined, and every question about what kind of integer
   `this` is would stop at the refinement and find no answer. And an ownership
   refinement that is not `_allocated` -- the only one PAL writes itself and
   the only one the model reads natively -- is now spliced under exactly the
   rule an `_inline_pulse` contract clause follows, and refused with exactly
   the same words when that rule says no.

   The net effect on the counts is a regression, and an honest one: dropped
   contracts went from 75 to 84 and six more bodies became untranslatable,
   because a contract that was never really there stopped pretending. All nine
   land in the `palow-old-annotations` backlog, since they are written against
   `Pulse.Lib.C.FuncPtr` and the old emitter's module names. `refine_fnptr`
   joined that backlog for the same reason. `test/refine_scalar_param` covers
   the half that is now genuinely supported: three functions whose refinements
   are load bearing -- without them no body can be shown not to overflow -- all
   verifying with no admits.

   With refinements on a value parameter working, a callback parameter follows
   directly, and this is the first place Palow says something the old
   translator has to be told. A function pointer's *value* -- which
   specification the code at that address meets -- is not carried by its bytes,
   so no points-to can grant it; it is the pure fact `is_valid f div pre post`,
   and the only way a body can call through a pointer whose target it does not
   know is for the contract to have handed one over. So a `_refine` granting
   `is_valid` on a function-pointer parameter is now taken at its word -- what
   else could it be granting? -- and licenses exactly that call. The pre and
   post are left to slprop matching rather than named: the fact in context is
   the author's, written in the author's words, and naming them here would mean
   reading those words.

   Such a refinement is stated at *both* ends of the contract, unlike a pure
   one. A pure refinement on a value parameter need not be restated on the way
   out, since the caller can derive it; but a resource is not a fact, and a
   body handed one and never asked to give it back would be left holding
   something it has no way to put down -- and a body that calls through the
   pointer twice needs it for the second call as much as the first.

   The other half is decay. Taking a function's address now *also* establishes
   what the code there does, as a ghost step beside the decay itself: it costs
   nothing, it cannot be wrong, and it means a concrete function can be passed
   straight to a callback parameter with none of the `_ghost_stmt` the old
   translator needs. What it does need is bookkeeping, because `is_valid` is
   `pure` behind a definition and Pulse will not absorb it unaided: a validity
   seeded while evaluating a call's arguments is put down after that call, and
   anything still held is put down when the function returns.

   One consequence had to be chased. `call_div` is in the divergent effect, so
   a body that calls through a pointer is divergent, and so is *its* caller --
   which is not known until that callee's body has been translated. The
   translation pass therefore repeats until the divergent set settles, in the
   same loop that already repeats until the call graph is acyclic.
   `test/fnptr_callback` covers the round trip: two callbacks, one taking a
   tuple and one not, each called both abstractly and with a concrete function
   passed in, all verifying with no admits.

   A smaller thing fell out of the same area. `const uint32_t *p = &g;` makes
   `p` an *alias* -- a name for the place `g` rather than an object of its own
   -- and using an alias as a value was refused outright, because handing out
   the value means handing out the focus that reaches the place, and a focus
   cannot outlive the statement that opened it. A global is the exception, and
   it is the exception for the same reason its address can appear in another
   global's initialiser: the address is a constant of type `ptr`, fixed for the
   whole run, so there is no focus to hand out and nothing escapes. Reading
   such an alias is now just the address. Seven of the eight admits in that
   cluster were globals; the one that remains genuinely is a local's.

   `break` and `continue` came next, and they turned out to be a question
   about a promise rather than about control flow: Pulse has both statements
   and they mean what C means. What Pulse also does, silently, is carry out of
   a `while` the fact that its condition is now false -- which is exactly the
   thing a `break` makes untrue, since it leaves from the middle, while the
   condition still holds. Pulse's own way of withdrawing that promise is an
   `ensures` clause on the loop, and a loop containing a `break` now carries
   `ensures true`. Nothing the source promised is lost by that: C makes no
   claim about a loop it jumped out of.

   What the author *does* claim at the exit arrives as `_ensures` on the loop,
   and here the two models part company. The old translator can put it
   straight into Pulse's `ensures`, because its locals are Pulse references
   and a specification may read one. Palow's locals are addresses, and every
   value a loop invariant talks about is bound existentially inside the
   invariant, so at the `ensures` there is no name for it. The claim is
   asserted just after the loop instead -- what holds at the exit is what
   holds immediately after it -- which costs the reads it names and means
   exactly what the source says. A `break` or `continue` that would jump past
   a local allocated inside the loop body is still refused, because neither
   statement runs the releases between it and the end of the body.

   Early `return` was the next thing, and it was already half done: a Pulse
   block is an expression, so leaving a function early means *being* the tail
   of what encloses you, and the translation already folded the statements
   after a returning `if` into the arm that falls through. What it did not do
   was believe its own construction. It asked whether a block leaves the
   function by looking at its last statement, which is wrong twice over: a
   `return` followed by the ghost statements that establish the
   postcondition is still a `return`, and an `if` both of whose arms leave is
   a block that leaves. And having built an `if` that is a value, it handed
   back no value for it, so a chain of early returns -- `if (d == NORTH)
   return SOUTH; if (d == SOUTH) return NORTH; ...` -- reported one arm
   producing a value and the other not.

   Both are now fixed, and the value is appended to the block rather than
   handed back, which is what makes a returning `if` a value in its own
   right. A `switch` in which every case returns follows for free. What is
   still refused is a `return` out of a loop, which needs a different shape
   than this one -- a flag, a `break`, and a test after -- and the message
   says so rather than blaming the `if`.

   A bug came out with it, of the kind only the second user of a mechanism
   finds. The validity of a function pointer, once seeded, is tracked so it
   can be put down again; but the tracking was not saved and restored across
   the arms of an `if`, so a validity seeded in the first arm was still
   believed to be held in the second, and the second arm tried to put down a
   fact about a function it had never mentioned.

   `goto` came next, and it turned out to be the same construction again.
   PAL's frontend has already recovered the structure -- a `goto` out of a
   block reaches the statements after that block, and the block knows its own
   label -- so what is left is that Pulse has no jump. It does not need one.
   The statements after a labelled block are recorded as that label's
   continuation, and a `goto` is translated by translating the continuation
   *there*, on the path that jumped. Falling off the end of a labelled block
   reaches the label exactly as a `goto` does, so the block is translated with
   a jump appended and the two cases become one. The `if` fold that carries
   early returns needed only to be told that a `goto` also leaves a block.

   The continuation is duplicated once per path that reaches the label, which
   is the price of not having a jump; the C this pattern comes from --
   `goto fail` and the unwinding ladder of `out_unlock: ... out_free: ... out:`
   -- has few enough of them that the generated code stays readable, and
   `test/multiple_goto`'s three-deep ladder verifies with no admits. Each path
   is typed on its own, which is why a label's `_ensures` -- the join
   condition the old translator needs to bring the paths back together -- has
   nothing to do here beyond being checked, and `_live` clauses have not even
   that, since the slots carry the storage already.

   `memset` was next, and it is the construct the byte-level model was
   supposed to make easy, so it is worth saying how easy it turned out to be.
   Zeroing an array needed one new axiom -- the machine layer can make a byte
   range all-zero, beside `memcpy`, which is the other place C admits that
   objects are sequences of bytes -- and one wrapper joining it to what the
   array layer already knew. That the elements then hold 0 is `encode_zero`,
   the lemma `calloc` already needed, and that every element's slice of an
   all-zero range is itself all-zero is `elem_bytes_zeroed`, which `calloc`
   also already needed. Nothing about `memset` is array-specific beyond those
   two, and nothing is per-element-type: the wrapper is generic in the
   element's representation relation, as everything about arrays in this model
   is.

   Only a fill of zero is covered, which is the fill C code reliably means --
   `memset` with any other value is well defined only for byte-sized types --
   and the fill is refused rather than guessed when the array's length is the
   caller's rather than settled here and the function has no translated
   `_requires` to settle it.

   Finding it cost more than writing it. A call to the new wrapper failed with
   "Application of a stateful computation cannot have a ghost effect", which
   says nothing about the cause: an implicit argument of a *non-ghost* Pulse
   function has to be one Pulse can erase, and the sequence the array holds
   was not marked `erased`. This is the second time that diagnostic has meant
   something other than what it says.

   The largest gap left in aggregates was storage for a structure with an
   array field. `struct guid { uint8_t bytes[16]; }` is the ordinary way C
   spells a fixed inline buffer, and until now such a structure had no
   automatic storage at all: every field shape but this one had a write-only
   view and an array had none,
   so declaring one as a local was refused outright. The missing view is
   `array_pts_to_uninit`, which hides the element sequence and keeps only the
   address and the length -- the length being the one thing the storage does
   determine, since `N` is part of the field's type. With that, four of the
   five generated storage operations stay what they were: claiming, revealing
   and forgetting an array field are folds, exactly as they are for a scalar.

   The fifth is not. Going from storage to holding a value genuinely writes
   bytes, and there are `N` of them to write, so filling an array field is the
   first piece of generated Pulse in this model that is a real computation
   rather than a rearrangement of what is already held. It is emitted once per
   *shape* -- element type, element size, length -- beside the structure that
   needs it, because the per-element write is per-type and there is no way to
   pass it as an argument.

   It is written as a recursion on the index rather than as a `while` loop,
   and that choice is the interesting one. A `while` in Pulse is divergent,
   and a divergent fill would make every function that declares such a
   structure divergent too -- a property of the memory model leaking into the
   specification of ordinary C code that merely has a buffer in it. A
   recursion with `decreases (N - k)` terminates, so nothing leaks. Reading a
   whole such structure is the mirror image, a second recursion accumulating
   the elements it has already read, ending in `Seq.lemma_eq_intro`.

   Two smaller things fell out. A brace initialiser for an array field is now
   a value: `{ 7, 9 }` for `uint8_t[16]` is a sixteen-element sequence with
   the tail zeroed, which needs the *target type* to say sixteen and so is
   read at the type rather than by `rvalue` alone. And a record literal names
   its labels without naming its type, so `{ fld_lo = 1 }` for a `struct pair`
   nested inside a `struct pairs` mentioned nothing that the scan deciding
   which modules to open could see. Modules now open what the modules they
   open need, which is the honest statement that F\* `open` is not transitive
   and these generated modules are one namespace.

   A local array with an initialiser followed, and it is the same shape of
   problem one level down. `char buf[] = "lo"` reaches the IR as a declaration
   and an assignment of a brace list that clang has already padded out to the
   declared length -- and an array is not assignable in C, so the assignment
   can only mean one store per element. Saying exactly that is the whole
   translation: each store goes through the element focus a subscript
   assignment already used, and the sequence the slot holds records what has
   been written, so `_assert(buf[0] == 'o')` afterwards is discharged by the
   same obligation any other read of a local array is.

   Passing that array to a function was the other half, and it is where the
   two views of an array meet. A local is held in the `option` view because
   its elements are written one at a time; a callee taking `T *` asks for the
   plain one, because it may read any of them. The conversion between them is
   two ghost steps with no bytes moving -- and the precondition of the first
   is precisely C's rule that reading an uninitialised object is undefined,
   which is to say that a local array may only be handed over once every
   element has been written. That is a proof obligation on the generated code,
   discharged from the sequence, and not a translator refusal. The way back is
   owed until the end of the statement, because it cannot be emitted until the
   call has been.

   Two addresses were being asked for that need not have been. `*(&x)` is `x`
   -- clang leaves the pair in the tree and nothing is loaded by it, so the
   address of a dereference of a reference is just the address underneath.
   And `&x` for a *named* object is a fixed address whatever happens to be
   stored in `x`: an assignment to `x` writes the object the alias already
   stands for, it does not change which object that is. Only a place computed
   *through* a name has to ask whether an intervening assignment moved it.
   Both were refusals where nothing was in doubt.

   A callback that takes a pointer was the next thing, and it is where the
   backlog of hand-written Pulse started to move. A `__fp` wrapper is the flat
   form `of_fn_div` can reflect -- `x:a -> y:erased c -> stt_div b (pre x y)
   (post x y)` -- and flat means no implicit binders, which is exactly what a
   pointer parameter has: the value the callee owns at it. So every wrapper
   was refused for anything but a function of values, and since a C callback
   is nearly always a function of a pointer, almost nothing could be decayed.

   The witness type `c` was put there for this and had never been used. Every
   implicit the specification has -- the value behind a pointer, the
   permission of a `const` parameter, a `_ghost_arg` -- is now a component of
   `c`, and the wrapper opens the tuple back up with a `let` inside its own
   contract, so the text of the contract is the text that was already being
   emitted. The caller of `call_div` then has to name the witness, and that is
   not an imposition: it is precisely the information an indirect call cannot
   infer from the pointer, namely which object the callee is about to be
   handed. In practice slprop matching sees it in the ownership being handed
   over, so the emitted call passes `_` and lets the match decide -- except
   when the witness is `unit`, where there is nothing to match and the one
   inhabitant is passed instead. Which of the two it is, is read off the
   function-pointer *type*: a parameter with a pointee contributes a witness
   component, one without contributes nothing.

   That needed a way for a test to say which model it is being translated
   for. Hand-written Pulse in a test names predicates, and the two models do
   not have the same ones; until now such a test simply carried a marker
   saying "not yet" and its fragments were dropped. `--palow` now defines
   `PALOW` for the preprocessor, so one source can carry both spellings under
   an `#ifdef` and be honest in both. `swap_struct` and `refine_fnptr` are the
   first two out of that backlog, and `refine_fnptr` in particular now
   translates with nothing admitted at all: the refinement granting
   `is_valid`, the wrapper carrying the callee's ownership, and the indirect
   call through it are all ordinary translated code.

   `_container_of` came next, and it is the clearest thing the flat pointer
   has bought so far. Recovering an enclosing structure from a pointer to one
   of its fields -- Linux's `container_of`, MsQuic's
   `CXPLAT_CONTAINING_RECORD` -- was, in the old model, a generated projection
   per field with two round-trip lemmas each, because a `ref` to a field and a
   `ref` to the structure were different kinds of thing and nothing related
   them but those lemmas. Here both are addresses, so the recovery is a
   subtraction and the projection back down is the matching addition, and the
   round trip is an equation about arithmetic rather than a generated axiom.

   The subtraction has to be total, and that is the one thing worth stating
   carefully. The offset fits only because the field pointer really does point
   into such a structure, and nothing in the pointer says so: `p` alone does
   not know it is `&s->f` rather than an arbitrary address. So `( -? )` is
   total in exactly the way `( +! )` already is -- forming a pointer is never
   an error here, only accessing through one -- and agrees with the refined
   `( -! )` wherever that is defined. What it is below zero is left
   unspecified, which is enough: a caller who knows the pointer came from a
   structure knows it as `base +! offset`, and `(a +! n) -? n == a` is then
   the whole round trip. Offset zero is the identity, which is what makes a
   first-member recovery NULL-preserving -- an intrusive list whose link sits
   at offset 0 is walked by recovering the node from the link, and the NULL
   terminator has to survive that or the walk never ends.

   `&s.f` became an address at the same time, and for a related reason: taking
   an address reads nothing, so it needs no ownership and no focus that would
   have to stay open past the statement. It is the structure's address plus
   the field's offset and that is all it ever was; the old refusal was an
   artefact of reaching for the machinery that *accesses* a field.

   `containing_record` is ported to this spelling and now states its contract
   rather than dropping it. What remains admitted there is honest and is the
   next cluster: a local that holds a pointer whose ownership the contract
   granted in the author's own Pulse is opaque to the emitter, which cannot
   see that the text covers the address the local holds.

   A pointer that is a fixed function of the parameters denotes one object
   for the whole call, and so a dereference of it is a parameter's dereference
   in every sense that matters. `addr` already lets a bare parameter's
   dereference through without asking who owns the target -- that is the
   contract's business and the frame matcher's to find -- and the same is now
   true of `_container_of(node, struct outer, node)` and of casts of such an
   expression. A pointer *loaded out of memory* is deliberately not admitted
   to this club: what it addresses depends on what was last stored there.
   `struct outer *parent = _container_of(node, struct outer, node);` is C's
   ordinary spelling of the recovery, and the local it binds is a name for an
   object rather than a pointer variable anyone stores through, so the alias
   map now records it as such.

   The value of an alias followed from that. An alias is a name for a place,
   and the *value* of such a name is the place's address -- which is not
   ownership: nothing is read by taking an address, no focus is opened, and
   whoever accesses through it still has to hold the permission. The old
   refusal ("whose place would have to escape") was inherited from a model in
   which a field's address could only be got by opening it. Aliases may now
   also be built out of other aliases, which is what a cast out to an initial
   member and back is made of.

   That round trip exposed the one place where a lemma is not enough.
   `add_sub_wrap` says `(p +! n) -? n == p`, but the Pulse frame matcher
   compares addresses as terms and does not call the solver, so a focus
   emitted at `((o +! off_in) +! off_x -? off_x) -? off_in` will not match
   ownership held at `o`. The cancellation therefore happens in the emitted
   text: subtracting an offset from an address that is syntactically an
   addition of that same offset just removes the addition.
   `struct_first_field_cast` and `struct_transitive_first_field_cast` are
   ported on that basis and translate with no admits at all -- including the
   two round-trip functions, which in the old model needed hand-written ghost
   `rewrite` bridges to re-address every cell the write touched, and in Palow
   need nothing, because the recovered pointer *is* the original address
   rather than a second name for it.

   `test/func_pointer` was the single largest pocket of annotations written
   against the old model -- 19 admits and 9 dropped contracts, a third of the
   whole backlog -- and porting it turned on three things at once.

   The first is a naming decision. Palow used to append the `__fp` wrapper to
   the function's own module, which meant a caller that only ever calls `g`
   directly still depended on the wrapper, and meant the wrapper had a
   different name in the two models. It now gets its own `Funcptr_<g>` module,
   which is what the old emitter already called it, so a `_refine` that names
   `Funcptr_add.func_add__fp` is the same text under either model.

   The second is that a hand-written fragment does not have to be duplicated
   just because the two models spell a library differently. An F\* module
   containing nothing but `include Pulse.Lib.C.Palow.FnPtr` re-exports every
   name in it, so a test can say `Fp_shim.is_valid` once and `#ifdef` only the
   two-line shim. The same trick names the two models' `int32_t` and its
   points-to predicate -- the old model's is a generated `Typedef_int32_t`,
   Palow's is `FStar.Int32.t` with no predicate at all -- and with that, some
   two hundred references collapse to one conditional. Where a fragment is
   pure scaffolding for the old model, an `_fp_ghost(...)` macro that expands
   to `_ghost_stmt(...)` only when `PALOW` is not defined removes it; a macro
   *around* an annotation works because clang resolves a macro argument's
   source range back to its call-site spelling, which is what PAL reads.

   The third is a genuine bug, and it is the seventh silent weakening this
   exercise has found. A slot remembers which function a pointer variable is
   known to hold, so that a call through it can be emitted as a direct call.
   That fact survived an `if` arm and was not joined, so a function that
   assigned `add` in one arm and `subtract` in the other emitted an
   unconditional call to whichever arm ran last -- code that would have
   verified and been wrong. It now joins to "unknown", the call is refused with
   a reason, and the count went up rather than down. The rule this confirms is
   the one the `_live` audit produced: any field that records *what I am
   currently holding* has to be saved and restored in both `tail_arm` and
   `branch`, and joined in both the `if` and the `switch` join.

   Two smaller emitter fixes came with it. `defined_names`, which decides a
   module's `open`s by reading the first word of every column-zero line, was
   reading spliced Pulse the same way -- and spliced Pulse is not indented the
   way generated code is, so a contract clause `requires ...` published
   `requires` as a name that module owned, and a continuation line `let x = e
   in` published `x`. Both made every other module open the splice, which F\*
   reports as a recursive dependency. A defined name now has to follow an
   actual modifier and may not sit on a line that continues a `let`. These
   only surfaced once the spliced modules stopped being dropped wholesale.

   A `__fp` wrapper is now also built for a function with a `_consumes`
   parameter. Nothing about the flat shape objected to it; the restriction was
   inherited from before the witness tuple existed. This is what a destructor
   stored in a vtable needs -- `void (*destroy)(struct itemx *)` whose
   implementation frees its receiver -- which is the shape `test/dpe` uses.
   `func_pointer` is down to 12 admits and 2 dropped contracts, and what is
   left is honest: calls through a pointer whose target is genuinely not known
   at the call site, and four uses of the old emitter's `$unfold` antiquotation.

   Four more tests came off the old-annotation backlog, and between them they
   say what the two models' pointer algebras cost to translate between.

   `container_of` existed to exercise the *pair* of inverse lemmas the old
   emitter generates for every field of every structure -- `container (proj p)
   == p` and `proj (container r) == r` -- one `container` symbol per field
   kind, aggregate, scalar, pointer and inline array alike. Palow generates
   none of them. A field's address is the structure's address plus the field's
   offset and the recovery is the wrapping subtraction of that same offset, so
   the left inverse is `add_sub_wrap`, one axiom covering every field of every
   structure at once, and it holds for the array field and the by-value
   aggregate field with no more said. That is the clearest case so far of the
   model doing in one line what the old one had to generate per declaration.

   The right inverse is where the two models genuinely differ, and Palow makes
   the difference visible rather than hiding it. `(p -? off) +! off == p` needs
   `off <= addr_of p`: at NULL it is false, because `(null -? off) +! off` has
   address `off`. The old model's `ref` algebra had nowhere to put that side
   condition and so implied it everywhere. `sub_wrap_add` states it, and is
   derivable from `ptr_ext` in three lines, so it is an abbreviation rather
   than an assumption. `container_field_read` -- the ownership move at the
   heart of MsQuic's `QuicAckTrackerOnAckFrameAcked`, where a caller owns a
   structure through a pointer to its embedded field and then reads that field
   back through the original pointer -- now states the premise in its own
   contract, as a `pure` fact about the field pointer it was handed. That is
   the same thing ISO C requires of `container_of` and the old model never
   asked for. Both tests translate with no admits.

   `fnptr_slprop_spec` needed no model work at all, only the shim the
   function-pointer port introduced: one `_include_pulse` naming "a `_plain
   int32_t *` holding zero" in each model's vocabulary, and the rest of the
   file is shared.

   `refine_uninit` turned out to be an emitter gap rather than an annotation
   one. `_refine_uninit` attaches a claim to storage the callee is handed
   *unwritten*, and Palow refused it on the grounds that an uninitialised
   points-to has no value for the claim to be about -- which is true, and is
   exactly why `$(this)` there can only mean the pointer. It is now translated:
   stated beside `<t>_pts_to_uninit`, on the way in only, since on the way out
   the storage holds a value and the predicate it qualified is gone. A
   `_refine_uninit` on a parameter that is not `_out` is reported rather than
   dropped, because there is no unwritten points-to for it to sit beside.
   Supporting it needed one fact the model did not have: unwritten storage is
   still storage, so `<t>_pts_to_uninit a` implies `a` is not NULL. That is
   what makes a `_out` parameter refined to be NULL vacuous rather than merely
   unprovable, which is what the test checks.

   Two things the count was saying wrongly have been separated out. A
   function declared in a header and defined in some other translation unit
   was being reported as an admitted body, which made the coverage number
   blame the translation for six functions it was never given any C for.
   There is nothing to verify about such a declaration: its contract is the
   promise the other half of the link makes, and the honest thing is to assume
   it in so many words. It is now emitted as `assume (pure False); unreachable
   ()` -- the same shape the existing emitter uses -- behind an `(* external:
   the contract is assumed *)` marker, and counted in a column of its own.

   `_refine_value` is translated. It is the annotation that says a pointer's
   invariant is not about the pointer but about some abstract value the
   invariant itself quantifies over -- a list of the elements reachable from a
   list head, the specification-level state of a DPE context, the validity of
   a function pointer stored in a field. Palow had been refusing it on the
   grounds that "it binds a name the contract machinery does not carry", which
   was true and is now false: the binder becomes an erased implicit on the way
   in and a fresh existential on the way out, exactly like the value of a
   pointee, and the clause itself follows the same split as every other
   refinement -- an `_slprop` is ownership and stands beside the points-to,
   anything else is a proposition and goes under a `pure`. That took seven
   contracts off the dropped list, including `func_pointer`'s cross-function
   dispatch through a struct field.

   It also revealed a limit worth recording. The name a `_refine_value` binds
   is in scope only inside the refinement that introduces it, so a function
   cannot relate that abstract value to its own arguments or result -- which
   is much of the reason to have one. Putting it in scope is a front-end
   change that would affect the existing emitter too, so it is left alone
   here; `inline_array_aliasing` states its aliasing claim in C instead, as an
   equation between two field reads, and that spelling is dropped and counted
   under the field-through-a-pointer gap rather than weakened in silence.

   Reading a union member is now allowed where the function's own
   `_requires` says that member is the live one. C says a union holds one of
   its members at a time and that reading a different one is not reading what
   you wrote, so the emitter had allowed the read only where it had put the
   value there itself -- which left every function that receives an already
   populated union unable to touch it. `u.m._active` translates now: Palow's
   union value is a tagged sum, so "which member is live" is which
   constructor the value was built with, and the clause is a discriminator
   applied to a value the contract already carries. The body then has a fact
   where it needs a shape -- the ownership in hand is stated at an opaque
   value and `focus` wants it stated at the constructor -- so the read is
   preceded by a `rewrite` between the two, which is sound exactly because
   the `_requires` said so and is unreachable without one. A claim under an
   implication or a disjunction is deliberately not collected: that is not
   something the body may rely on unconditionally.

   Two things fell out of doing this. A union nested in a struct was not
   reachable at all, because the step that opens whatever aggregate holds a
   place only opened struct-typed fields; and the lines closing that
   aggregate were being dropped on the union path, which would have left the
   struct in pieces past the end of the statement. Both are fixed, and
   `union_test2` -- five spellings of the same read, through a value, a
   pointer, a nested struct, and an alias to the nested union -- translates
   and verifies with no admits.

   Recursion works. A `_rec` function carrying a `_decreases` measure now
   comes out as Pulse's `fn rec ... decreases (...)`, and its own body may
   call it. Everything needed was already there -- Pulse has total recursive
   functions, the IR carries `is_rec` and the measure -- and all that was
   missing was to stop the cycle-breaking machinery from treating the
   self-edge as a cycle. That machinery exists for the real problem, mutual
   recursion, which the per-declaration module layout has nowhere to put: two
   functions that call each other would have to be emitted as one definition
   in one module. Direct recursion needs none of that, so a function whose
   measure translates is excused from it, its self-edge is dropped before the
   sort sees it (a module never opens itself), and a call to itself is no
   longer refused. Recursion without a measure still is, which is the honest
   answer: C gives nothing to prove termination with.

   The measure has to be written in specification arithmetic --
   `(_specint) hi - (_specint) lo`, not `hi - lo`. This is the same rule
   Palow applies to every contract: machine arithmetic in a specification is
   refused because `Int32.v (a + b)` is not `Int32.v a + Int32.v b`, and a
   measure is a specification. It is a rule worth keeping here even though a
   `decreases` clause carries no meaning of its own, because a measure read
   with wrapping arithmetic can decrease when the real quantity does not. The
   existing emitter accepts the same spelling, so `rec_fn` and
   `recursive_functions` say it once for both models.

   Assertions got three things they were missing. `_assert(u.m._active)`
   works now: a contract can read a union's tag straight off the value it has
   a binder for, but a body deliberately keeps no binders, so it names the
   union's current value the only way it can -- asserting the ownership it
   already holds, binding the witness, and applying the discriminator to
   that. `_assert(false)` works, which sounds trivial and is: C has no
   separate notion of truth, a condition is a number and holds when the
   number is not zero, and the fallback had only ever accepted `_Bool`. And
   a `_let` function may be named in an assertion, which is not making a call
   -- a `_let` is an F\* term, nothing runs -- so it reads as the term it is,
   with specification-typed arguments translated as mathematical values
   rather than machine ones.

   Doing that turned up a rule applied one place too widely. Signed machine
   arithmetic is refused in a specification, because `Int32.v (a + b)` is not
   `Int32.v a + Int32.v b` and a contract boundary offers nothing to rule the
   overflow out. But the *body* of a `_let` or a `_pure` function with its
   own `requires` is not a boundary: F\* checks that body under the
   precondition, which is exactly where such an obligation is discharged. So
   those two bodies now allow it, and `double_int_spec(int x)
   requires(int_fits((_specint) x + x))` is an F\* definition rather than a
   function nobody may mention.

   Calls through a function pointer held in a struct or union field work
   now, which is to say dispatch tables work. There are two ways to know what
   the code at an address does, and both were only being looked for one level
   up. The first is that the emitter watched the store: it already remembered
   which function a *local* held, and a vtable is a struct whose fields are
   code pointers, so the record became per-field -- keyed by the path within
   the slot, the empty path for the slot itself. A brace initialiser is read
   out the same way, since `struct ops o = { .op = add };` is a dispatch
   table written in one statement. Nothing is loaded at such a call: knowing
   the store means the address is the decay, and passing the decay rather
   than a load keeps `is_valid` and the callee the same term, which is what
   slprop matching needs.

   The second is that the contract said so. A spliced ownership `_refine` on
   a function-pointer parameter was already taken at its word; a spliced
   `_refine_value` on a pointer is now taken at its word too, and that is
   exactly the shape a vtable's invariant has -- the struct's value is
   quantified over and the clause says what the code in its fields does. Here
   the field *is* loaded, and the load is what makes it work: it is the
   identity on the state and carries a `rewrites_to`, so the address handed
   to `call_div` is the term the `is_valid` in context is stated at.

   Two smaller things fell out. `union u; u.m = x;` needed a way to make a
   member active starting from storage that has never held anything, so
   unions now generate a `switch_uninit_<m>` beside `switch_<m>`; the proof
   is the same one, since only the length of the storage is used. And
   ownership stated at a `_plain` `_consumes` parameter was being restated on
   the way out, which is wrong -- the caller handed it over for good. There
   is no points-to to read that off, so the mode is now consulted directly,
   and validity gathered at an indirect call through such a parameter is put
   down rather than left over.

   A local struct is built one field at a time, and between the first
   assignment and the last it is neither storage nor a value. The focus
   operations cannot say that -- a focus opens a value and puts the same
   value back -- so the object is *scattered* into its fields' storage on the
   first write and *gathered* back into a value on the last, with each field
   in between written through its own address and nothing open around it.
   Both halves are generated per struct and both proofs are a single
   `unfold` or `fold`: `_pts_to_uninit` was already field-by-field, which is
   the whole reason this works. A third operation, `_gather_uninit`, is the
   way back for an object that went out of scope half-built -- each written
   field gives its value up on its own and what is left is the storage the
   local started with.

   This is what the old model's source-level `$unfold-uninit` was for, so
   under `PALOW` that annotation is now a no-op macro in the one test that
   uses it. One wrinkle came with it: a validity seeded for a function stored
   into a struct field, and then handed to a call inside that struct, comes
   back stated at whatever value the callee's postcondition binds. The term
   that was seeded is no longer a term in scope, so such a fact is put down
   by shape rather than by name -- but only that one, since a validity the
   contract granted has to survive to the end.

   The two linked-list tests come off the backlog. Their predicate is a
   recursive `is_list` written by hand in inline Pulse, and it turned out to
   be almost model-independent: what it needs from the model is "the object
   at this address", "the right to free it", and "a points-to rules out
   null". Naming those three once behind `#ifdef PALOW` keeps a single copy
   of the predicate and its three ghost lemmas, which is the honest way to
   read the result -- the reasoning is the same, only the vocabulary moved.
   Palow now generates a `_pts_to_not_null` per struct for the third, which
   is worth having anyway: a predicate over a linked structure is exactly
   where the null case has to be ruled out, and the caller has no reason to
   know which field sits at offset zero.

   Two front-end things had to give. A `_letimpure` accessor -- `_elements_of(l)`,
   the list `l` denotes -- is impure by construction and has no F\* definition
   to call. The old model emits it as a `ghost fn` with `requires pure False`
   and calls it inside its `with_pure` notation: a way of writing a value that
   cannot be computed. In Palow the value is already bound, as the erased
   implicit the parameter's `_refine_value` quantifies over, so a call to such
   an accessor is read as a mention of that binder. This is also the answer to
   the scoping limitation recorded above: the binder cannot be named directly
   in the function's own contract, and `_letimpure` is the name for it.

   And a `_refine_uninit` reached above a pointer rather than below it was
   dropping the whole contract. Where the annotation sits says which storage
   it is about: below a pointer it is the pointee's, which an `_out`
   parameter is handed and which any other pointer parameter really would be
   losing; above one it is the object's own, and a parameter passed by value
   has none. There is nothing there to say, so nothing is lost by not saying
   it -- which is what the old translator does with it too.

   String and compound literals get the treatment C's storage-duration rule
   asks for. A literal is an object with static storage duration, so what the
   expression denotes is nothing more than an address: `literal_addr xs` in
   the pointer layer, indexed by the contents rather than by the occurrence,
   since C leaves it unspecified whether two identical literals share storage
   and a program may rely on neither answer. Deliberately no ownership comes
   with it. A literal is read-only and shared, and the only use of one this
   model can justify is handing the pointer to a callee that promised to hold
   nothing -- so the translator refuses a literal in any argument position
   whose parameter is not `_plain`, which is visible as a refusal rather than
   left for F\* to discover as a missing points-to.

   That is a deliberate divergence from the old model, which stack-allocates a
   fresh array, copies the literal into it, and frees it after the call. That
   works, and it is what lets `write("hello", 6)` go through today, but it
   hands the callee a writable object where C has a read-only one, and it
   gives the literal automatic storage where C gives it static. The two calls
   in `stringlit` that need ownership of a literal stay admitted until there
   is a read-only sharing predicate to give them; the three that only need the
   address -- a returned name, a `_plain` argument, a `switch` selecting one
   of several names -- now translate in full. Array-to-pointer decay became
   the identity in the process, which it already was for every other array:
   Palow names an array by the address of its first element, and the
   ownership, which is what really differs between the two, is not part of
   the value.

   A struct field whose type is an array now decays like any other array: to
   the address of its first element, which under Palow is the field's own
   address. Nothing is read by taking one and no ownership changes hands --
   whoever accesses through the pointer still has to focus the field out of
   the struct, which is where the obligation belongs. That is the whole of
   what the old model needed a decayed handle for, and it comes out as
   arithmetic rather than as a different kind of value.

   Emitting those bodies exposed a gap that had been hiding behind them. A
   `_plain` pointer parameter owns nothing by itself: whatever ownership it
   has comes from a `_refine_value`, and the all-or-nothing contract drop
   takes that away along with everything else. A body that went on
   dereferencing such a parameter was asking Pulse for ownership its own
   signature no longer stated -- a generated file that fails rather than a
   weaker one, which is the one outcome the measurement discipline does not
   allow. Parameters are now tracked by whether the emitted `requires` really
   owns the pointee, and a dereference of one that it does not is refused and
   counted. A contract with hand-written ownership in it is taken as a grant
   over everything, which is the same trust a spliced clause gets everywhere
   else: what a `_preserves` written in Pulse covers is the author's business
   and not something Palow can read.

   `free` had one more case than the block bookkeeping knew about. A block
   is something this body allocated and can therefore see the size of; a
   `_consumes _allocated` parameter is a block someone else allocated and
   handed over, and its size is already written into the signature as a
   `freeable`. The two are the same obligation reached by different routes,
   so the emitter now recognises the second as well: a `free` of such a
   parameter forgets the typed view, reveals the bytes underneath, and
   returns them. That is what a destructor is, and until now every
   destructor in the suite -- `sum_and_free_point`, `destroy_impl` -- was an
   admit for want of it.

   A struct's two predicates. C's `struct simple { int x, *y, **z; }`
   describes three fields but four objects: the struct, `*y`, `*z` and `**z`.
   Palow's `_pts_to` is deliberately the first of those and nothing else -- it
   says which bytes the object occupies and what values they encode, and a
   pointer field's value is an address, not an object. That shallowness is
   load-bearing: it is what makes a byte-level view of the same storage agree
   with the field-wise one, and it is what lets a struct be an array element
   or a union member at all.

   But almost every C struct holding a pointer means to own what it points at,
   and a function taking one has to be able to say so without writing the
   conjunction out by hand. The old model answered this by folding the two
   together -- one generated predicate that owned the fields *and* everything
   reachable through them, against a flattened record of all their values.
   Palow keeps them apart instead. Each struct now also gets an `_own`
   predicate over its *value* rather than its address: `_own x p s` claims the
   objects the pointers in `x` reach, and `s` records what is in them. The
   two are independent conjuncts, which is what makes deep ownership optional
   -- holding a bare `_pts_to` is still a legitimate and much cheaper thing to
   do -- and it is also the only way the two can carry different fractional
   permissions, which is what sharing a structure while mutating through one
   of its pointers needs.

   Three kinds of pointer field own nothing, and that they are a *question* at
   all rather than a projection is the interesting part. `_plain` says the
   field is a bare address; `_core_ref` says the pointer exists to break a
   cycle and carries no predicate by construction; an array pointer points at
   an extent nothing here knows, so there is no amount of memory to claim. A
   `_nullable` field is excluded for a different reason: its ownership is
   real but sits behind a guard, and an unconditional conjunct would be a
   claim about a null pointer. The walk follows a chain of owned pointers as
   far as it goes -- `**z` is two objects, and the second one's *address* is
   the first one's *value*, which is why an item's address may mention the
   record being defined -- and stops at a struct or union, claiming its
   `_pts_to` but not what it in turn points at. Following that would need the
   pointee's module, which for a mutually recursive pair does not exist yet,
   and would make a self-referential struct's predicate infinite. Stopping is
   the same choice C makes when it asks for a forward declaration.

   A contract states both halves, and a body opens the second one when it
   needs it. A struct pointer parameter now carries `_own` alongside
   `_pts_to`, which is what makes the two models comparable
   annotation-for-annotation: the old one's single generated predicate owned
   the same objects, just folded into one. The interesting half is the body.
   Deep ownership is held *folded*, because that is the form a contract
   states and a call passes; a statement that reaches through a pointer field
   scatters it, uses the pieces, and gathers them back before the statement
   ends. Bracketing it per statement rather than per function is what keeps
   every branch, loop and call seeing the same shape, and it costs nothing at
   runtime because both directions are ghost.

   The item names do the addressing. `_own`'s record is named after the path
   that reaches each object -- `z` for what `s->z` points at, `z_1` for what
   *that* points at -- so resolving an access is a walk of the same shape over
   the expression, and `**s->z = 42` comes out as a field read, a pointer
   read, a write, and the two ghost brackets around them. The parameter is
   the only root a walk starts from: what a struct reached any other way owns
   is not something this signature states, and saying so is the same refusal
   as everywhere else in the emitter.

   A refinement on a struct *declaration* is a fact about every value of that
   type, and it was being thrown away. `struct _refine(this.x == 1) b` says
   something true of every `struct b` anywhere -- a parameter of that type, a
   pointee of a pointer to it, a callback that takes one -- and until now
   Palow could only report that it had nothing to do with it. That cost the
   by-value case everything: a struct passed by value owns nothing, so the
   refinement is the only thing its contract could possibly say, and dropping
   it left `read_positive` with `requires emp` for a function whose whole
   point is that its field is positive.

   The machinery for stating it already existed -- a `_refine` written on a
   parameter goes through the same path -- and what was missing was only the
   collection step and one question about what `this` means. On a by-value
   parameter it is the value, which is what the existing path already does.
   On a pointer it is the *pointee*: the declaration writes `this.x`, not
   `(*this).x`, because it is talking about the struct and not about whatever
   happens to hold it. So the clause is bound at the pointee's type and to the
   pointee's value term, which differs at the two ends of the contract exactly
   as the pointee itself does. `on_b` and `apply_b` in `refine_fnptr` now
   carry the refinement through an indirect call, which is what that test was
   written to check.

   The generated ownership then needed two corrections before it could be
   widened. The first is that `_plain` suppresses it. `_plain` says the
   declaration's ownership is the author's business, and it is as often
   written on the typedef that names a struct as on the struct itself; both
   spellings now suppress the generated predicate, because otherwise a
   hand-written `_refine` and a generated `struct_X_own` would claim the same
   memory twice. The second is that a struct passed *by value* also gets the
   deep ownership: the pointers it holds are the same pointers whether the
   struct arrived by value or through an address, and a by-value parameter had
   no way to say what they reach.

   The pointers that reach an extent rather than one object can now be owned
   too. An `_array` field contributes `array_pts_to` over a sequence whose
   length the predicate deliberately does not fix -- a struct that knows its
   own length says so in a `_refine`, and that refinement is a clause about
   `Seq.length` of this very sequence, so pinning it in the predicate would be
   saying the same thing twice in a place where a struct without such a
   refinement could not follow. `b32_struct` and `mixed` now carry their
   arrays' ownership through every call.

   That last change was what first made the deep predicate's matching
   fragile, and the fix is worth recording because it is a general hazard. A
   struct field's general unfocus hands the struct back as a record rebuilt
   field by field, which is the original only up to eta. F\* proves that
   without complaint, but Pulse finds `struct_X_own` in the context by
   matching on the struct *value*, and a rebuilt record does not match
   syntactically. Reading through an array field therefore now closes with the
   field's read-only unfocus, which returns the struct at the very value it
   had.

   An `_array` field's ownership is then something a contract can read. Its
   sequence is the only place its length can come from, so `this.x._length`
   is `Seq.length` of the ownership record's field, and `a.x[i]` is
   `Seq.index` of it -- neither is in the struct's *value*, which holds only
   the pointer. The ownership record is looked up by the struct's value term
   rather than by the parameter, because that is the one spelling the three
   ways of naming a struct -- by value, through a pointer, or as `this` in the
   struct's own `_refine` -- all agree on. A loop invariant gets none, since
   it binds a fresh value whose ownership it has no name for yet, and says so.

   A body can reach the same storage. A subscript of an `_array` field reads
   the pointer out of the field and focuses the extent the deep ownership
   claims, inside the same scatter/gather bracket the pointer fields already
   used -- widened here to a struct passed by value, whose value term is the
   parameter itself. One gap showed up doing it: a `return` is not routed
   through the statement emitter, so whatever the returned expression unfolded
   was never folded back, and the frame release that follows is stated in
   terms of the folded predicate. It closes explicitly now. All of
   `refine_struct` -- `b32_arr`, `set_elem`, `copy_elem` -- has a real body and
   a real contract for the first time.

   A follow-up found the same mistake in three places. An annotation is as
   often written on the typedef that names a struct as on the struct itself,
   and resolving a typedef is not the same as looking past the `_refine` the
   typedef carries: `array_test`'s `b32_struct` is exactly `refine_struct`'s,
   spelled the other way, and it got no ownership, no contract and no body
   because three lookups stopped at the annotation instead of the struct
   under it. They peel now, and `array_test` is down to its one untranslated
   allocation.

   Taking an address had been conflated with reaching through one. `&p->f`
   reads nothing, so it needs no ownership at all -- an address in Palow is
   inert until a points-to for it is produced, and an access through it asks
   for that separately -- but it went through the same path as an access and
   so demanded that the function hold `*p`. There are two questions here, and
   there are now two answers: one for an access, which must know the storage
   is held, and one for arithmetic, which must not care.

   `containing_record`'s `value_proj_null_fires` is the case that shows why it
   matters, and it also shows the model doing without something the old one
   needed. Recovering a first member's address from a structure pointer has to
   preserve null, or an intrusive list walk could never detect its terminator;
   the old model emitted a `proj_null` axiom per field to say so. Palow emits
   nothing: the projection is `p +! 0sz`, and that a zero offset moves no
   pointer is arithmetic the model already knows.

   An `if` can carry an `_ensures`, and until now Palow dropped it: Pulse
   computes the join of an `if` by itself, so an annotation that says only
   what is live is a check and not a necessity. An annotation that states
   *ownership* is a different thing. A function-pointer local assigned a
   different callee in each arm has no common description that the emitter can
   invent -- each arm knows a concrete function, and only the author's own
   words say what the two have in common -- so the annotation is the join.
   Palow now emits it, with one caveat learned the hard way: Pulse does **not**
   frame an `if`'s annotation. Anything live and unmentioned is left over, so
   the emitted annotation has to be the whole state at the join, which is the
   author's clause plus the generated frame for everything they did not speak
   for. Which slots the author spoke for is read off the `$&(x)` antiquotations
   in the clause; an `$(x)` is a *read*, and a read still needs the frame to
   say what is there.

   Validity is the resource that makes this worth doing. `is_valid` is carried
   by no points-to -- the bytes of a code pointer say where the code is, not
   what it does -- so before this milestone a call through a local whose target
   was decided by a branch could not be translated at all. Now a clause that
   speaks for such a local is what makes the call possible, and the validity it
   establishes is recorded as held by the body and put down at the end with
   everything else. Because the clause binds a fresh name for what the slot
   holds, a validity that was seeded at a concrete function is no longer
   spelled that way once the clause has been proved, and it has to be put down
   by inference rather than by name.

   C11 makes a compound literal an lvalue, which is why a named constant is so
   often a macro expanding to one, and why the base of a member access is so
   often a literal rather than a variable. Palow had been sending such a read
   down the same path as any other field access, which asks for an address and
   finds none. A structure is a record value here, so the read is simply the
   projection -- no address, no ownership, nothing to focus. The literal's
   record has no type of its own, so the projection has to say which record it
   is, and an ascription does that.

   The same lvalue-with-no-name shows up as an argument, and there it is a
   string literal: `write("hello", 6)` passes an anonymous array with automatic
   storage. A `_plain` parameter is content with the literal's address and
   asks for nothing else, which is what `literal_addr` has always given it, but
   an `_array` parameter wants the elements -- and the only thing that can hand
   those over is storage. So the literal now gets storage, and the translation
   is exactly the one a declared local array already had: allocate, write the
   elements, free it with the rest. The name it is allocated under is invented
   here, because C never gave it one.

   Two of the tests whose hand-written Pulse was written for the old model are
   now written for this one, and what they had to say came out shorter. PAL's
   `_arrayptr` names an interior pointer, and the old model needed a predicate
   relating it to the array it came out of -- `arrayptr_pts_to p arr`, plus
   arithmetic about `offset_of` on both. Here a pointer *is* an address, so the
   cell an accessor returns is `table +! (sizeof(E) * idx)` and that equation is
   the whole postcondition; and a function handed an interior pointer is handed
   a run of cells starting at it, which is the ordinary array contract with a
   `_requires` saying the run is not empty. Both dropped contracts became real
   ones, and `set_x_via_ptr` got a body.

   That last one also uncovered a plain bug. `p->f` where `p` is an array
   parameter is `p[0].f`, and the code that says so was focusing the element
   out of `*p` rather than out of `p` -- so it asked for the subscript of a
   dereference and refused itself. No test had reached it before.

   The `weaken_generalize` test moved over too, and it is the first one whose
   hand-written Pulse is a *specification* rather than a proof step: it gives
   two functions with different contracts a single common interface, so that
   one caller can invoke either through the same pointer. The old model's
   version of this needed `Pulse.Lib.C.FuncPtr.weaken` and a `prevent_lifting`
   wrapper around the postcondition it had to re-establish; this model's
   `weaken` does not, so the four witness-map lemmas became bodies that do
   nothing. The one thing that did need care is that a function pointer here
   may carry more than one `is_valid` at once -- one at the wrapper's own
   contract, from the store that put the address in the slot, and one at the
   common contract, from the `weaken`. Dropping the second cannot be written
   `drop_is_valid _ _ _`: with two candidates in the context the underscores
   have nothing to pick by, and the proof state names both. Naming the
   predicates is enough. All three of its dropped contracts and both of its
   admitted bodies went away.

   `ghost_fnptr` was the largest backlog entry and moved over almost
   mechanically, which is itself the interesting part. Its subject is the
   *witness* a function-pointer wrapper quantifies -- the erased data a callee's
   contract needs that its arguments do not carry -- and the old model splits
   that witness in two: an "elim" half, one component per pointer argument
   whose existential the wrapper had to eliminate, and a "ghost" half, one per
   `_ghost_arg`. Palow has no elim half. A points-to is stated at an address,
   and an address is an argument, so nothing has to be existentially
   quantified to state the precondition; the witness is a single flat tuple of
   values. The weakening the test exercises pins two of its components, and
   what was `fst (snd y)` and `snd (snd y)` over a nested pair is now
   `Mktuple4?._3 y` and `Mktuple4?._4 y` over one. The identity post-coercion
   that `weaken` demands also loses its `prevent_lifting`, for the same reason
   it did in `weaken_generalize`.

   Two things fell out. A direct call to a function with `_ghost_arg`s was
   refused outright; in this model a ghost argument is an ordinary erased
   implicit at the end of the signature, and the caller's own points-to pins it
   by matching, so the refusal was never justified and removing it cost
   nothing. And a `_refine` written on a struct *field* -- which is how this
   test advertises that the `m` field of a `struct ops` is a valid function
   pointer -- turned out to be ignored silently. That is a real weakening of
   every contract mentioning such a struct, so the struct's module now says so.
   Eight of them exist across the suite, in `dpe`, `fnptr_spec` and here; the
   two bodies still admitted in `ghost_fnptr` are downstream of exactly that
   gap and of the allocator-null deviation.

   The other half of that field-level `_refine` then went in, because a note
   saying "not stated" is only worth having once it is as narrow as it can be.
   A refinement written on a field is an invariant of the struct *type*, so it
   reaches a contract exactly the way a struct-level one does: every parameter
   of the type carries it, with `this` standing for the field rather than for
   the whole struct -- `(reveal val_b).fld_n` through a pointer, `var_b.fld_n`
   by value. `test/refine_field` is the new acceptance test; its `twice`
   discharges an `int32` overflow obligation that nothing else in the contract
   could. What remains uncovered, and what the struct module's note now says,
   is narrower: the generated ownership does not *carry* the invariant, so a
   value of the type that arrives any other way -- a return, a local, a global
   -- does not have it. That is why `ghost_fnptr`'s call through a returned
   `struct ops *` is still admitted.

   As of this milestone: **915 specifications, 836 of them with real bodies,
   63 admitted, 16 external, 73 functions skipped**, plus **18 `_pure`
   functions emitted as F\* terms** (15 definitions and 3 `assume val`s). The generated `swap` is
   line-for-line the
   hand-written `swap_addressable` in `Examples`, which is the check that
   mattered.

   Emitting this much settles the part of the port that carries the model
   decisions, and demonstrates the payoff claimed in the overview: a
   parameter's F\* type is `ptr` regardless of how the pointer is used, so the
   pointer-kind inference in `elab` has nothing left to decide.

   The `admit()` reasons, in order, are what to do next. Inline Pulse (35) has
   to be re-expressed against the new predicates and is a source change, not a
   translator change. An indirect call through a pointer whose target the
   emitter cannot see (6), a call through a function pointer (4) and a missing
   `__fp` wrapper (2) are three problems rather than one: a callback
   parameter's contract arrives in a `_refine` written as inline Pulse, a
   local struct's field needs the target noted per path, and a function with a
   pointer parameter needs a witness type in its wrapper. Signed arithmetic is refused on purpose: its
   overflow obligation is discharged by the `_requires` clause, and emitting it
   where that clause did not translate would produce failures that say nothing
   about the memory model. Seven more are functions this file only *declares*,
   whose `admit()` is the trusted specification and not a gap.

   Three of the remaining clusters have a design in them rather than just work,
   and it is worth writing them down before starting.

   **An array local.** `int a[10];` needs storage the same way a struct local
   does, but element by element rather than field by field, and the elements
   are not initialised together. The neat way to say this is to reuse
   `array_pts_to` at a different representation:

   ```
   let maybe_repr (t_repr: t -> bytes -> prop) (esize: nat)
                  (x: option t) (b: bytes) : prop =
     match x with
     | None   -> len b == esize
     | Some v -> t_repr v b
   ```

   An array local is then `array_pts_to (maybe_repr t_repr esize) esize a 1.0R
   xs` for `xs: Seq.seq (option t)`, and *every* existing combinator --
   `array_split`, `array_join`, `array_focus`, `array_unfocus` -- applies
   unchanged, because none of them looks at the representation. Allocation is
   one generic proof and needs no unrolling per length: `mem_stack_alloc
   (esize * n)` gives `esize * n` bytes and `Seq.create n None` is the
   sequence they represent. A write to `a[i]` focuses the element, goes down to
   raw bytes, comes back up through `t_write_uninit`, and unfocuses at
   `Seq.upd xs i (Some v)`. A read needs `Some? (Seq.index xs i)`, which is
   exactly C's rule that reading an uninitialised object is undefined -- and
   note that it becomes a *proof obligation* rather than a translator refusal,
   which is the right shape: the emitter stops having to track initialisation
   at all, and the sequence carries it.

   The same predicate is what a partially initialised *struct* local wants, and
   for the same reason. The `init` flag on a slot is per object; a struct wants
   it per field, and the honest way to get that is for each field's points-to
   to say whether it holds a value, not for the translator to remember.

   **A function pointer.** `Pulse.Lib.C.FuncPtr` already models one, and
   nothing in it is about memory: a `func_ptr a b` is an abstract *value* with
   a pure `valid f div pre post` relation to a Pulse specification. That part
   transfers to Palow unchanged. What was missing is the storage: a function
   pointer held in a local, a field or an array needs a representation in
   `sizeof(void (*)())` bytes, and the question was whether that should be one
   representation per C function type -- matching `sizeof`, and matching how
   every other type is handled here -- or a single opaque code-pointer pattern
   that a cast reinterprets. *Settled: a single type.* A function pointer is
   just a `ptr`, by the same argument that collapsed the type-indexed reference
   type: it is what an implementation does, it is what provenance already says
   about an address, and it makes storage free rather than a per-function-type
   axiom. The spec a pointer satisfies is not carried by its representation but
   by the separate pure `valid` relation, so nothing is lost -- recovering a
   stored callback's spec was never going to come from its bytes anyway.

   **A mutable global.** An immutable one is published as an F\* constant and
   needs no ownership, which is why it works today. A mutable one has storage
   that outlives every function, so someone has to own it, and C gives no
   syntax to say who. The two candidates were an invariant -- correct for a
   global a concurrent program shares, but it forces every access into an
   atomic block -- and a `pts_to` that the caller passes in, which matches how
   the rest of Palow works but means the contract of every function that
   touches a global grows a conjunct the C source never wrote. *Settled: pass
   the `pts_to` in.* The awkwardness is real and lands entirely at `main`,
   which has no caller to get the ownership from; in exchange the model can
   express the lifecycle real C programs actually have -- uninitialised, then
   unsynchronised mutable access from the main thread during start-up, then
   synchronised or read-only access from every thread -- which an invariant
   fixed at one shape cannot say at all. The remaining piece is static
   initialisation: until a global's initialiser can be published at any type,
   an owned global arrives at an arbitrary value, so only the globals this file
   actually writes are owned.

   `_pure` functions are F\* definitions, not Pulse `fn`s. This was the last
   structural divergence from the existing translator, and it mattered for the
   same reason it does there: a `_pure` function is the vocabulary a contract
   is written in, so it has to be a *term* an `_ensures` or an `_assert` can
   mention. Pulse rejects a `fn` in a specification -- "cannot find
   rewrites\_to in post" -- because a computation has no value until it is
   sequenced. So a `_pure` definition is translated to
   `let func_f (var_x: T) : Pure R (requires ...) (ensures fun ret -> ...) = e`,
   where `e` is the body as one expression: an `if` becomes `if/then/else` with
   the continuation duplicated into both arms, and a local becomes a `let`.
   The contract translator is reused verbatim for the body, which is the point
   -- a pure body and a specification are the same language. When the
   definition does not come out (inline Pulse, an untranslated `_requires`) the
   function falls back to the Pulse `fn`, so only specifications that mention
   it are lost, not the ability to call it. 15 of 17 `_pure` functions in the
   test suite come out as definitions, including the recursive ones, whose
   `_decreases` becomes F\*'s. A `_pure` function that is only *declared* here
   -- `pal_c_assert_enabled` in `pal.h` is the one that matters -- becomes an
   `assume val` at the same type, which is a term too and so may equally be
   mentioned in an `_assert`; a caller could rely on nothing but the contract
   in either case.

   Nothing is ever lifted out of an `_assert`. An `_assert` is a
   specification: it does not run, and translating it must not make the program
   do something it would not otherwise do. Turning `_assert(f(x) > 0)` into
   `let t = f x; assert (t > 0)` adds a call, and a C function may have side
   effects, so an assertion that calls a function which is not `_pure` is
   refused rather than rewritten. A loop guard is the opposite case: `while
   (f(i))` calls `f` on every iteration, so lifting the call out would run it
   once, and Pulse accepts a computation in the head of a `while`. The guard
   therefore keeps the call exactly where the source put it, which is what
   makes the six functions of `test/func_call_guard` translate.

   Three narrower fixes came with it, each a case of a wrapper hiding a type.
   `resolve` follows typedefs but deliberately not the annotation wrappers, so
   `_plain int32_t *` never reached the pointer case of the operator table and
   `a == b` on two `_plain` pointers was refused as "an operator on a pointer"
   even though `ptr_eq` was right there; operators and literals now go through
   a `peel` that strips `_plain`, `_refine` and `_nullable` as well, since an
   operator is chosen by the underlying scalar type alone. `true` and `false`
   are macros for the literals `1` and `0` at type `_Bool`, so integer literals
   had to be given a `_Bool` case. And C's conversions to and from `_Bool`
   -- `(_Bool) n` and `(int) b` -- are now translated in contracts, neither
   being able to lose information.

   Substituting a read back into an `assert` is only sound for a read.
   The rule had been "if every line the operand emitted was a simple `let`,
   inline them all", which is right for `t_read` (whose postcondition says
   `rewrites_to`) and wrong for a call (whose postcondition says nothing of the
   sort). The two are now distinguished, and a call keeps its binding.

   Three things about *contracts* were wrong, and between them accounted for
   more admitted bodies than any translator feature.

   A contract that measures signed arithmetic now says the mathematical
   result. `_ensures(return == a + b)` had been refused outright, on the
   principle that a contract must not describe an operation the body would not
   perform; but that is the wrong reading. Signed overflow is undefined, so on
   every program C defines `Int32.v (a `+` b)` and `Int32.v a + Int32.v b`
   agree, and the second is a total term whose typing does not need the
   `_requires` -- which matters, because Pulse does not have the `requires` in
   scope when it types the `ensures`. Unsigned arithmetic wraps and is
   defined, so it keeps its operator. C has no negative literals either, so
   `-1000` arrives as a negation of `1000` and had to be recognised as the
   literal it is. Together these unblocked 15 bodies.

   `NULL` is the integer literal `0` at a pointer type, and is translated to
   `null`. Any other integer at a pointer type is manufacturing an address,
   which the model deliberately does not let a program do.

   `_plain` means the function owns nothing behind the pointer. Palow had
   been granting a points-to for every pointer parameter regardless, which is
   exactly backwards: `_plain` is the annotation a source writes precisely so
   that a caller may pass `NULL`, and the existing translator emits no slprop
   for it. The bug was invisible until `NULL` became translatable and
   `check_null(NULL)` turned into an unprovable `int32_t_pts_to null`. Dropping
   the grant *raised* coverage by nine bodies, because a weaker contract is
   easier to call; a body that dereferences a `_plain` pointer is now refused,
   which is what the annotation asked for. `_nullable` is refused for the same
   reason, and will stay refused until `unless_null` appears in contracts.

   Subscripts are translated. `a[i]` on an array parameter is not a read but a
   six-line sandwich -- discharge the offset's `fits` fact, `array_focus`, trade
   the generic element predicate for the type's own, do the machine operation,
   trade back, `array_unfocus` -- and that is the honest cost of a byte-level
   model: the array really is in pieces for the duration of the access. All six
   lines are mechanical, and the model was shaped so that they can be: the value
   never appears in them, so the emitter never has to name `Seq.index xs i`.
   `*p` on an array parameter goes down the same path, since it is `p[0]`.

   Two obligations are not the emitter's to discharge. `i < Seq.length xs` can
   only come from the function's own `_requires`, so a subscript in a function
   whose contract did not translate is refused (7) rather than emitted to fail.
   The offset's `esize * i` needs to fit in a `size_t`, which `array_offset_fits`
   derives from the ownership itself. `test/palow_array` covers reads, writes,
   a read and a write through one array, and two arrays at once.

   The dropped contracts are a shorter list, and none of them is about memory.
   Arithmetic on machine integers inside a contract (32) is refused because
   `Int32.v (a + b)` is not `Int32.v a + Int32.v b`: for unsigned types the C
   operation wraps, and for signed ones the equality holds only under the
   no-overflow assumption that the surrounding contract is there to establish.
   Distributing it would silently change the specification, so it waits for a
   translation that carries the modulus. Inline Pulse (17) and calls to
   functions whose own contract is not translated (13) are the same problems as
   in the bodies.

   Structs are translated, and the generated shape is a deliberate departure
   from the byte-level definition in `Pulse.Lib.C.Palow.Aggregate`. There a
   struct's points-to is one `mem_pts_to` over the whole object with a `_repr`
   relating it to the field values, and the split is a chain of `mem_split`s
   plus enough `slice` reasoning to line the pieces up. That is the right
   definition for reasoning about representation -- type punning needs it -- and
   the wrong one to generate, because then every field access would carry that
   proof.

   So `struct_S_pts_to` is generated *as* the separating conjunction of its
   fields' points-to predicates, and the split and join are an `unfold` and a
   `fold`. Per field there is a hole predicate and a focus/unfocus pair, which
   is the same triple the array combinator has, on purpose: a field access and
   a subscript are the same operation on a sub-range and the emitter should not
   have to tell them apart. The byte-level view is still reachable -- each
   field's `t_reveal` gives its bytes and `mem_join` puts them back -- but
   deliberately rather than by default, which is the principle the scalar layer
   already follows.

   What the generated shape does not say is anything about padding: a struct's
   ownership is its fields', not its bytes, so it falls short of the whole
   object by however many bytes clang inserted between the fields. That is
   enough for field access, which is all the translator does with it. A
   whole-object `memcpy`, a `free`, or an array of structs needs the byte-level
   `_repr`, and arrays of structs are refused for exactly that reason.

   A fixed-size array field is the one field shape that is not a single
   points-to. In C `T f[N]` inside a struct is N elements of storage rather than
   a pointer, so the field owns a whole `array_pts_to`, and its length goes into
   the record type as `(s: Seq.seq T { Seq.length s == N })` rather than into a
   side condition -- which is what makes `Seq.upd` through it obviously
   length-preserving. Focus and unfocus are unchanged: only the predicate a
   field owns differs, not how it is opened.

   That makes `s->f[i]` a composition of two focuses, and it is worth noting
   where the bounds obligation comes from in each. An array *parameter*'s length
   is whatever the caller passed, so `i < Seq.length xs` can only come from the
   function's own `_requires`, and a subscript in a function without one is
   refused. An array *field*'s length is in its type, so it needs no help at
   all.

   The other thing this exposed is that ownership has to come from somewhere.
   `s->next->x` and `**p` read a pointer *out of memory* and then dereference
   it, and nothing in the translated contract grants ownership of what it points
   to; the caller would have had to say so in a `_requires` that is not
   translated. Such dereferences are refused with that reason rather than
   emitted to fail. Only a parameter's pointee is owned, because only
   parameters appear in the contract. `test/palow_struct` covers reads, writes,
   two fields of one struct, mixed field widths, and two structs at once.

   Merging the main line brought four tests that exercise function pointers
   and mutable globals harder than anything before them, and each found
   something.

   An indirect call now writes its witness out as a tuple spine. The witness
   is the tuple of implicits the callee's wrapper quantifies -- one component
   per pointer parameter, saying which object it is being handed -- and the
   caller does not have to know the values: the ownership in its context says
   what they are, and slprop matching reads them off. What it does have to
   know is the *shape*, because Pulse solves a hole standing for a witness
   leaf but not one standing for a whole tuple: the projections the callee's
   contract applies to it cannot reduce until the hole is a real tuple, so a
   single hole stays stuck no matter what the context offers. Writing `(hide
   (_, _))` instead of `_` turns one stuck hole into two solvable ones, and
   the emitter built the wrapper, so it knows the arity. A one-component
   witness was already inferrable, which is why this only showed up once a
   test called through a pointer to a function owning two objects.

   A mutable array global now publishes its address. Palow had emitted a
   module only for an array global that is `const` with a known initialiser,
   on the reasoning that such an array is a sequence constant and not an
   object; but the address is what a contract naming the array needs, whatever
   is stored there. Without it the generated contracts referred to a name
   nothing defined. Ownership is unchanged -- it is threaded by hand through
   `_live` and assumed at the entrypoint -- and the address is the only thing
   the declaration has to contribute.

   An array subscript now checks that its bound is available before emitting.
   The rule was already there for an array *parameter*, whose extent is
   dynamic and whose bound can only come from the function's own `_requires`;
   the path that reaches a global array had been left out, so a body with a
   dropped contract would index into it and fail. A constant index into an
   array whose extent is in its type still goes through, since it carries its
   own bound.

   Two of the new tests are on the backlog rather than translated: their
   hand-written Pulse -- in one case a whole directory of it -- is written
   against the old memory model, and they carry the marker that says so.
   `Pulse.Lib.C.Palow.FnPtr` gained the `weaken` generalization across witness
   types and the `frame` axiom that the main line added to its counterpart,
   so the two function-pointer libraries stay in step.

   A contract can now talk about a mutable global's contents, and not only
   about holding it. The conjunct that hands the ownership over already named
   the value -- `gval_g` before, `gval_g'` after -- so all that was missing
   was letting a specification reach it: `g[i]` and `g._length` now resolve
   against that binder exactly as `p[i]` and `p._length` resolve against a
   pointer parameter's. Nothing in the translation of a pointee ever depended
   on there being a pointer; what it needs is a term for the contents, and the
   ownership conjunct supplies one. A loop invariant says it with the same
   words, which it should, an invariant being a contract about one point in
   the body.

   An array global whose extent this file does not know -- `extern T g[]`,
   sized in the defining unit -- is owned like any other array. The extent
   only refines the sequence's length, and where it is absent a contract that
   needs a bound states one, as it must for an `_array T *` parameter anyway.
   Such a global is also kept rather than dropped as immutable: the rule that
   a global nothing here stores through is better published as a value than
   owned assumed there was a value to publish, and for one declared `extern`
   there is not -- the initialiser is in another unit. `_live(g)` in the
   source is the author asking for the ownership, and that is now enough to
   keep it.

   GNU's `a ?: b` translates at every type Palow has. It is an infix
   operator like any other -- `a \`elvis_int32\` b` -- because PAL binds the
   left operand to a name before applying it, so what the definition
   duplicates below its `if` is a value and not a computation, which is the
   whole content of "evaluated once". On a pointer it is the one truth test C
   has that is not a comparison with the integer zero, and under Palow the
   only form it could take: a pointer's value is not a number, so "nonzero"
   can only mean "not null".

   An array reached through a second name is the same array. `T *p = a;` is
   C's array-to-pointer decay, and it copies nothing: `p[i]` and `a[i]` name
   one object. Palow used to give `p` a slot of its own, which meant loading
   from `a` as if it were a pointer and then owning a pointer whose pointee is
   an element -- ownership no contract grants, and none has to, because the
   contract already granted the array. Such a local is now recognised as a
   name rather than as storage, exactly as an alias `q = &x` already was, and
   its declaration and its one assignment emit nothing. In the same spirit a
   subscript may now be the base of a field access, `a[i].f`, for every kind
   of array the emitter knows -- a parameter, a local, a mutable global, an
   allocated block -- and not only for an array parameter, which is the one
   case the old gate happened to ask about.

   A mutable global's name is a value in a contract. The conjunct that hands
   its ownership over already names what it holds; all that was missing was
   letting `x` in a specification mean that name, as `*p` already meant the
   pointee of a pointer parameter. An array global is deliberately not
   included: there the name is a decayed pointer and not a value, and
   `buf[i]` reaches the contents by the route it already had. With that,
   `test/global_mutable` -- read, write, read-modify-write, a call that
   threads the permission, a write through `&x`, and a struct-typed global
   whose fields the postcondition constrains one at a time -- translates with
   nothing dropped.

   A `sizeof` in a contract is the same literal the body emits. Milestone 3
   made every size a concrete number from clang's ABI, which is exactly what
   makes `return == sizeof(int)` provable rather than merely consistent, but
   the contract translator had never been taught the two expression forms.
   Along the way it became clear that a size needs no *representation*:
   `sizeof(double)` and `sizeof` of a union with a `double` arm are answerable
   numbers even though Palow models neither type, so clang's layout for every
   aggregate is now recorded whether or not the aggregate is modelled.

   A partial operator states its own definedness. C's shift is undefined
   when the count reaches the width, and its signed arithmetic when the
   result does not fit; the source says so in a `_requires`, and a body may
   lean on that clause because Pulse puts it in scope. A *contract* clause
   may not: F\* types the clauses independently, so `return == (a << b)` was
   an application whose own typing had nowhere to look, and the whole
   contract was dropped -- which then took the body's `_requires` with it and
   cost an admit as well. The obligation is now stated in the clause that
   needs it, conjoined to its own left: `p /\ q` types `q` with `p` assumed,
   which is precisely the scope the application was missing. The clause is
   then a stronger statement than C's and provable from the `_requires` that
   motivated it -- and `size_t`, whose F\* operations are the checked ones,
   owes exactly the same thing.

   A cast from a specification type reads as the number it already is. PAL
   writes `arr[(size_t) ((_specint) (len - j) - 1)]` when the author wrote
   `arr[len - j - 1]`, and that cast has no content: the mathematical integer
   is what was meant. Reading it that way rather than as `SizeT.uint_to_t n`
   is not merely simpler but necessary, because the alternative carries a
   typing obligation the clause cannot discharge -- a guard conjoined at the
   top of a clause cannot mention a variable the clause binds itself, and
   these casts appear under exactly such a `_forall`. `test/reverse_test`'s
   specification now translates in full.

   A loop body is a scope. Declarations inside one never reached the
   environment, so the first use of such a local failed to typecheck and the
   whole function was admitted -- which is why `test/reverse_test`, the
   showcase for array ownership, had no body at all. Extending the
   environment as the body's statements go by, and releasing the storage they
   declare at the closing brace, is what a branch already did; a loop simply
   had not been given it.

   With bodies emitted, two things that had never been exercised turned out
   to be wrong. `_old` inside an invariant meant the current iteration's
   value rather than the function's entry state, which for `reverse` made the
   invariant say every element equals itself -- a statement that is both
   useless and false of a half-reversed array. It now resolves to the
   signature's own ghost binder, which is in scope throughout the body and is
   what `_old` means everywhere else.

   And an invariant covered every local in scope, which is a disaster for the
   ones the body does not touch: a local bound existentially and constrained
   by nothing is a local whose value the loop has forgotten. Pulse's frame
   rule already carries what the body leaves alone, and carrying it *outside*
   the invariant is the only way its value survives. The invariant now covers
   exactly the locals the body may write and the ones a clause names, which
   is why an inner loop no longer destroys what the outer one knows --
   `test/do_while`'s nested `continue` is the case that found it. Invariants
   got considerably shorter as a side effect.

   `test/reverse_test` -- an in-place array reversal with a real invariant
   over the permuted contents -- now translates and verifies end to end.

3. **Done for `sizeof`/`alignof`.** Sizes and alignments now come from clang's
   target ABI and are emitted as concrete `SizeT` literals;
   `Pulse.Lib.C.Sizeof` is deleted. Field offsets are collected from clang too
   but are not consumed yet — they are what milestone 4 needs.
4. **Done for structs; unions and byte-level struct `_repr` remain.**
   Aggregates: struct `*_repr` and field split/join with and without padding,
   the generic array combinator with per-element focus, flexible array members,
   and unions with the type-punning acceptance test. The translator now
   generates a Palow type per struct -- record, layout constants, points-to and
   per-field focus/unfocus -- and translates field access in bodies and field
   projection in contracts. What remains is the byte-level `_repr` per struct,
   which arrays of structs and whole-object copies need, and unions.
   Fixed-size array fields are covered; bit-fields are not, since the model has
   no sub-byte addressing to give them a byte offset.
5. **Done for single objects.** `malloc`/`calloc`/`free` are ordinary
   specifications and the translator emits calls to them: `malloc(sizeof(T))`
   is a `malloc t_sizeof` and nothing about `T` reaches the emitter except its
   size. What remains is array and flexible-array allocation, `free` of a
   `_consumes` parameter, deleting the `Malloc`/`MallocArray`/`MallocFlex` IR
   nodes, and deleting `_core_ref`.
6. *Done for the model.* Custom allocators, with their own `freeable`
   predicates.
7. **Done for the model.** `exposed` / `uintptr_t` round-trips, `memcpy`, and
   stored pointers (`ptr_repr`, `ptr_read`, `ptr_write`). What remains is
   emitting casts between pointers and `uintptr_t` from the translator, which
   is blocked on milestone 2.
8. **Done for the model.** Effective types: `ctype`, the per-byte index,
   `access_ok` and the store rule, with the union, array and integer/pointer
   punning theorems. The index is reserved in layer 0 as `mem_pts_to_at` but is
   not yet enforced by the typed loads and stores.
