# PAL surface syntax

PAL programs are C files annotated with macros declared in `pal.h`. Under `-DC2PULSE` each macro expands to a Clang `__attribute__((annotate("pal-...")))`; without it the macros vanish and the file compiles as ordinary C.
These macros are used to give specifications to types and functions.
This document explains how to write these specifications using PAL; `palow.md` describes the memory model the generated Pulse is written in.

In the following, we differentiate between two kinds of annotations:
1. `_requires` / `_ensures` / `_invariant` / `_refine` are used to add specifications for functions and types as well as loop invariants.
2. When these annotations are not enough for specifying some function or for progressing the proof then PAL provides annotations such as `_ghost_arg`, `_ghost_stmt`, `_assert`, `_inline_pulse`, `_include_pulse` that reach the Pulse layer directly when the surface syntax isn't enough.

Ownership is generated: every pointer parameter's contract owns what it points at, every struct passed by value owns what its pointer fields reach, and every loop invariant carries the locals and pointees that are live across it. The annotations below change that default or add to it.

## Variadic calls with an ignored tail

PAL supports direct calls to variadic functions whose bodies do not access
the variadic arguments. The generated function and its calls contain only
the fixed parameters; extra arguments do not transfer ownership to the
callee.

For this initial support, ignored arguments must be literals (including
string literals), integer constant expressions, non-volatile/non-atomic scalar
or pointer local/parameter values, addresses of ordinary local variables or
parameters (including a local array, which decays to its address), or
computations over those that cannot be undefined: integer conversions, `~`,
`&`, `|`, `^`, unsigned `+`, `-` and `*`, and unsigned shifts by a constant
smaller than the width. Parentheses and implicit value conversions (including
default promotions) are allowed. Dereferences, member/subscript reads,
division, signed arithmetic, side effects, and other unsupported extra
expressions are rejected rather than silently skipping their evaluation.
Indirect variadic calls and variadic argument extraction are not supported.

For example, `read_first(int *first, ...)` may return `*first`, and a caller
may use `read_first(&a, &b, &c)`. Only `&a` is passed in the generated Pulse
call. See `test/variadic_call/variadic_call.c`.

## Syntax for specifications

### Annotating function arguments
For every function, PAL by default adds pre and post conditions for every argument: the precondition requires ownership of what the argument points at, and the postcondition returns it (with an existentially quantified new value). The default fits most cases; the annotations below override it. Pointers are `ptr`, and ownership is stated with the predicate generated for the pointee's type (`int32_t_pts_to`, `struct_s_pts_to`, `array_pts_to`, ...). For `T *x` the default is

```
fn func_f (var_x: ptr) (#val_x: erased T)
  requires T_pts_to var_x 1.0R val_x
  ensures  exists* (val_x': T). T_pts_to var_x 1.0R val_x'
```

| C syntax                  | implicit resource in `requires` / `ensures` |
|---------------------------|---------------------------------------------|
| `T *x`                    | `T_pts_to var_x 1.0R val_x` at both ends (new value `val_x'` on the way out) |
| `const T *x`              | `preserves T_pts_to var_x perm_x val_x`: a fraction, and the value is unchanged |
| `_plain T *x`             | nothing: `x` is a bare address; the user supplies any ownership in `_requires` / `_ensures` |
| `_plain T x` (a value)    | nothing: for a struct, neither the `_own` of its pointer fields nor its type's or fields' `_refine`s; only refinements written on the parameter itself are stated |
| `_consumes T *x`          | `T_pts_to` in `requires` only — not returned |
| `_out T *x`               | `T_pts_to_uninit var_x` in `requires`, `T_pts_to` in `ensures` |
| `_nullable T *x`          | `unless_null var_x (T_pts_to var_x 1.0R val_x)` at both ends |
| `_allocated T *x`         | adds `freeable var_x <size>`: the block came from `malloc` and may be freed (usually with `_consumes`) |
| `_array T *x` / `T x[]`   | `array_pts_to T_repr <size> (SizeT.v T_alignof) var_x 1.0R val_x`, `val_x : Seq.seq T` |
| `_arrayptr T *x`          | nothing: a pointer into an array owned elsewhere (stated by hand, see `test/arrayptrs`) |
| `struct s x` (by value)   | `struct_s_own var_x 1.0R own_x` when `struct s` has owned pointer fields |
| `_core_ref T *f` (a field)| nothing: a non-owning back-pointer, left out of the struct's `_own` |

`_nullable` and `_allocated` also apply to the return value: `_allocated _nullable T *f(...)` is the shape of an allocator.

The body may dereference a `_nullable` parameter only where a null test on it has settled that it is not null: in the matching arm of `if (p)`, `if (p != NULL)` or `if (!p) return ...;`, of `p ? ... : ...`, or on the right of `p && ...` / `p == NULL || ...`. The translation opens the guard there (`elim_unless_null`) and closes it again where the arm ends. A contract still cannot mention `*p`, and a `_refine` behind the guard keeps the body from opening it.

Beyond ownership, the user typically also wants to constrain values. PAL provides the following annotations for adding extra contract clauses:

- `_requires(p)` / `_ensures(p)` — extra pre / post predicates on a function.
- `_preserves(p)` = `_requires(p) _ensures(p)`.
- `_preserves_value(x)` = `_ensures(x == _old(x))`.
- `_invariant(p)` / `_ensures(p)` on a loop — see below.
- `_decreases(p)` — termination measure on a `_rec` function (required there; not a loop annotation).
- `_assert(p)` — verification assertion inside a function body.

Inside any of these predicates the following spec-only constructs are available:

- `_old(x)` — value of `x` at function entry.
- `*p`, `p->f`, `a[i]` — the value behind a pointer, read off the contract's existential (`val_p`, `(val_p).fld_f`, `Seq.index val_a i`); no read is performed.
- `x._length` — length of an `_array`'s sequence (`Seq.length val_x`).
- `_live(x)` — the storage of `x` exists. For a local in a loop invariant, or a parameter, the generated frame already says so, and `_live` translates to `True`; for a mutable global it is the global's points-to (see below).
- `_specint` — arbitrary-precision integer (ghost arithmetic); `(_specint) e` turns a machine integer into a mathematical one, so overflow bounds can be stated.
- `_slprop` — type cast that declares a separation-logic predicate (in `_refine`, or on an `_inline_pulse` clause).
- `$(...)` — antiquotation: splice a C-level entity into an `_inline_pulse` body (see the Antiquotation section under Pulse interop).

Builtins with a Pulse model may be used in specifications too, e.g. `__builtin_bswap64(x)` is `Pulse.Lib.C.UInt64.bswap64 x`.

### Loop invariants

Loops (`while` / `for` / `do-while`) carry their own contracts via `_invariant` and `_ensures`. PAL generates the ownership part of the invariant — one existential per live local and pointee — and adds every `_invariant(p)` clause, reading each C name as the existential's value. So an invariant usually states only the facts:

```c
uint32_t acc = 0;
for (uint32_t ctr = 0; ctr < x; ctr = ctr + 1)
  _invariant(ctr <= x && acc == ctr * y)
{
  acc = acc + y;
}
```

lowers to:

```
while (((uint32_t_read loc_ctr) `UInt32.lt` var_x))
  invariant exists* (inv_acc: UInt32.t) (inv_ctr: UInt32.t).
    uint32_t_pts_to loc_acc 1.0R inv_acc **
    uint32_t_pts_to loc_ctr 1.0R inv_ctr **
    pure ((UInt32.v inv_ctr <= UInt32.v var_x) /\ (UInt32.v inv_acc == UInt32.v (inv_ctr `mul_wrap` var_y)))
{ ... }
```

Inside `_invariant`:

- Parameters and locals are in scope by name; there is no `this`. `_old(x)` is the value at function entry.
- `_live(x)` is accepted but unnecessary (the frame is generated).
- Ownership PAL does not generate — a helper predicate, part of an array named through an `_arrayptr` — goes in an slprop clause: `_invariant(_inline_pulse(Helpers.claim $(lo) $`arr))`. `` $`name `` there is quantified by the invariant (see `test/arrayptrs`).

`_ensures(p)` may also be attached to a loop. It states what holds when the loop exits. Without a `break` the loop exits only when the condition is false, and the clause is asserted after the loop. With a `break`, Pulse no longer knows the condition is false on exit, so:

- if the loop body contains no nested loop, PAL mirrors the locals the `_ensures` names in ghost references and states it as the loop's Pulse `ensures`: it is proved at every `break` and at the normal exit;
- otherwise the loop gets `ensures true`, and the `_ensures` must follow from the invariant alone.

```c
while (i < n)
  _invariant(i <= n)
  _ensures(i <= n)            // proved at the `break` and at the normal exit
{
  if (i == limit) { break; }
  i = i + 1;
}
```

A `break` or `continue` that would skip the release of a local declared inside the loop body is not translated; declare such locals before the loop.

For `do { ... } while (cond)`, PAL desugars to `while (first || cond)` with a fresh boolean flag. Use `_do_while_first(name)` to name that flag explicitly when the invariant needs to refer to it, or `_do_while_cond(name)` to name the continuation flag (see `test/do_while/do_while.c`).

### `if` statements

Pulse computes the state after an `if` itself, so an `if` needs no annotation. An `_ensures` on an `if` is emitted only when it states ownership (an `_slprop` clause): it is then the join, and PAL frames in the points-to of every live slot the clause does not name with `$&(x)`. A pure `_ensures` on an `if` is not emitted; use `_assert` after it instead.

### Refinements for data types

PAL generates predicates for compound types (`palow.md`). These can be further enriched with user-supplied predicates carried by the type itself:

| annotation                  | when the predicate must hold              |
|-----------------------------|-------------------------------------------|
| `_refine(p)`                | when the value is initialized             |
| `_refine_always(p)`         | always, even when uninitialised           |
| `_refine_uninit(p)`         | only when uninitialised (`_out` parameters) |
| `_refine_value(bind, pred)` | as `_refine`, but binding name is `bind`  |
| `_refines(p)` (on a field)  | as `_refine`, with the struct's other fields in scope by name |

A refinement does *not* change the runtime representation. A pure refinement is stated as a `pure` conjunct beside the ownership of a value of that type, wherever the contract states that ownership (parameter, pointee, return value), at both ends. A refinement cast to `_slprop` is ownership: it is stated in `requires`, and also in `ensures` unless the parameter is `_consumes`.

**On a typedef** — the refinement fires for every use of the typedef.

```c
_refine(this._length == 32) typedef _array uint8_t *uds_array;

void f(uds_array a) { ... }
// requires array_pts_to uint8_t_repr 1 (SizeT.v uint8_t_alignof) var_a 1.0R val_a
// requires pure (Seq.length (reveal val_a) == 32)
```

`_refine_always` on a typedef is the form to use when the type also appears in `_out` position, since the refinement then has to hold in the uninit precondition too.

**On a struct declaration** — `this` is the whole record; reach into fields with `this.<field>`. The annotation must be written *after* the `struct` keyword, otherwise clang ignores it.

```c
struct _refine(0 < this.x) simpler { int x; };

void f(struct simpler *s) { ... }
// requires struct_simpler_pts_to var_s 1.0R val_s
// requires pure (0 < Int32.v (reveal val_s).fld_x)
```

`_plain` on a struct declaration suppresses the generated `_own` predicate, which is how a record-level `_refine(_inline_pulse ...)` can replace it outright — see [`test/refine_struct/refine_struct.c`](../test/refine_struct/refine_struct.c):

```c
struct _refine(_inline_pulse (int32_t_pts_to $(this.y) 1.0R $(this.x)))
    _plain selfref { int x; int *y; };
```

Record-level annotations on `union` declarations are not supported yet; use a typedef for those.

**On a field type** — the refinement applies to that field's value; `this` is the field, not the surrounding record. A pure field refinement is also part of the generated record type (`fld_x: v:Int32.t{0 < Int32.v v}`), so every value of the struct satisfies it. A field refinement cast to `_slprop` — typically `Pulse.Lib.C.Palow.FnPtr.is_valid` on a function-pointer field — is stated in the contract of every function holding the struct, and makes calls through the field possible (see `test/fnptr_spec`).

```c
struct s {
    _refine(0 < this) int x;
};
```

### Ghost code

PAL exposes two ghost constructs for proof assistance that have no runtime effect:

- `_ghost_arg(T name)` — extra parameter erased at runtime; usable only in specs and ghost statements.
- `_ghost_stmt(expr)` — Pulse statement executed only during verification (e.g. applying a lemma).

Ghost arguments do not change C function-pointer signatures. Generated
wrappers forward them through erased witnesses. If inference cannot determine
a call's ghost arguments, supply a witness with a ghost statement,
`_ghost_stmt($witness (hide (a, b)));`, immediately before the call, direct
or indirect; the callee's precondition must still hold. Taking a function's address requires no witness.
See `test/func_pointer/func_pointer.c` for examples.

## Pulse interop

- `_inline_pulse(expr)` — embed a Pulse expression in a spec position. Cast it to `_slprop` (or `(bool)`) to say what it is when that is not clear from context.
- `_include_pulse(Mod, snippet)` — drop a verbatim Pulse block (definitions, lemmas, helpers) into a module `Mod`.
- `_let(sig, body)` / `_let_rec(sig, body)` / `_letimpure(sig, body)` — Pulse-level top-level bindings.
- `_type(name, body)` — Pulse-level type definition.

### Antiquotation

Inside an `_inline_pulse(...)` body — and the spec macros built on it — text is emitted to Pulse **verbatim**; antiquotations are the `$`-prefixed forms PAL rewrites into C-level entities (`exists*`, `**`, `pure`, module names, etc. pass through untouched).

| form | emits |
|------|-------|
| `$(expr)`                                 | the **value** of a C expression — variable, `*p`, `x.f`, `_container_of(...)`, `this`, `return`. A pointer's value is its `ptr`, so `int32_t_pts_to $(p) 1.0R v` is about what `p` points at |
| `$&(expr)`                                | the **address** of a C lvalue — a local's storage (`uint32_t_pts_to $&(n) 1.0R v`), or a field's (`$&(s->len)`) |
| `$type(c-type)`                           | the F* type for a C type (`$type(int *)` is `ptr`, `$type(struct s)` is `struct_s`) |
| `$field(Type::f)`                         | a struct field accessor (`fld_f`), or a union field constructor |
| `` $`ident ``                             | `'ident` (an F* implicit / ticked name); in an `exists*` position, a fresh existential of inferred type. Infix: `` pfx$`sfx `` → `pfx'sfx` |
| `$declare(Type id)`                       | nothing — binds `id : Type` in the annotation's scope so a later `$(id)` resolves |
| `$unfold(T)` / `$fold(T)`                 | the ghost step that splits a struct into its fields / joins them again (`struct_T_scatter` / `struct_T_gather`) |
| `$unfold-uninit(T)` / `$fold-uninit(T)`   | the same for uninitialised storage (`struct_T_scatter_uninit` / `struct_T_gather_uninit`) |
| `$unfold(U::f)` / `$fold(U::f)`           | the unfold / fold step for union field `f` |
| `$scattered(struct T) $(p)`               | nothing — says `*p` is already in pieces, as after `T_scatter_uninit`, possibly with fields the body does not write holding values; the body's field writes then fill the rest by address (`write_uninit`), and `*p` is gathered only if every field gets written |
| `$gathered(struct T) $(p)`                | nothing — the closing form of `$scattered`: says a ghost step has made `*p` whole again, so later accesses focus its fields instead of filling them |
| `$witness <term>`                         | nothing — in a `_ghost_stmt` immediately before a call, `<term>` is the tuple of ghost arguments that instantiates the callee's contract; only the author knows it, so the call site has to say it. Before a direct call it is the erased tuple of the callee's `_ghost_arg`s, in order (`hide 5ul`, `hide (1ul, 2ul)`); everything else is inferred |

Notes:

- **Context sensitivity.** A parameter is a value (`var_p`), and a local lives at an address (`loc_x`). `$(x)` of a local in body position (a block / `if` `_ensures`, a `_ghost_stmt`) reads it first and substitutes the result; in a loop invariant it is the invariant's existential (`inv_x`). Use `$&(x)` to talk about a local's storage.
- **Special names.** `this` (inside `_refine*`, the value being refined; reach fields with `this.f`) and `return` (inside `_ensures`, the returned value).
- **Field accesses are automatic.** PAL focuses a field before reading or writing it and unfocuses afterwards, and scatters / gathers a struct being initialised field by field; `$unfold` / `$fold` are only needed when your own ghost code wants the pieces.

`test/antiquot/antiquot.c` exercises every form.

## Function attributes

- `_pure` — function has no effects; callable in spec position.
- `_total` — the function terminates. Accepted, but currently ignored: function pointers are always the divergent kind (`of_fn_div`, `call_div`).
- `_rec` — recursive (must be paired with `_decreases`).
- `_memset_zero` — the function is a `memset(p, 0, n)` wrapper, and calls to it are translated as such (`test/memset`).
- `_pulse_opaque_to_smt` — on a pure global, emit its value `opaque_to_smt`, so that a large initializer is not unfolded by the SMT solver (`test/global_array_tactic`).

## Global variables

A global is either **pure** (immutable) or **mutable**, and the two are modeled
very differently. A global is pure when *either*:

- it is annotated `_pure`, or
- it is `const`-qualified — this is implicit, no annotation needed. An
  initializer is *not* required.

A global with no initializer is still pure if it is `const` or `_pure`: with no
initializer anywhere in the translation unit it is a *tentative definition*
(C11 6.9.2p2) and is initialized as if by `0` (6.7.9p10) — arithmetic types to
zero, pointers to null, aggregates field- and element-wise. That zero is the
value the emitted definition takes, so such a global reads as `0` and PAL can
prove it. An incomplete initializer is filled out the same way, so
`const struct point s = {.x = 1};` reads as `{1, 0}`.

```c
_pure uint32_t g_a = 42;      /* pure, explicit  */
const uint32_t g_b = 7;       /* pure, implicit — same treatment as g_a */
const uint32_t g_c;           /* pure: tentative definition, reads as 0 */
uint32_t       g_d = 1;       /* mutable: not const, not _pure */
```

Every global has an address, published as an assumed `ptr` in its module
`Global_g`:

```fstar
assume val addr_var_g : ptr
assume val addr_var_g_not_null : squash (not (is_null addr_var_g))
```

Assuming the address is what C says — a global has one fixed address for the
whole run — and it is why `&g == &g` holds definitionally. `&g` is supported
in any expression position.

### Pure globals

A pure global is also a plain F* value, and every read of it is
**ownership-free**: the read evaluates to `var_g`, with nothing in the
`requires`. A read through `&g` is resolved to the same value:

```fstar
let var_g_b : UInt32.t = 7ul
assume val acquire_var_g_b : unit -> stt_ghost unit emp_inames emp
  (fun _ -> exists* (p: perm). uint32_t_pts_to addr_var_g_b p var_g_b)
```

An array global's value is a `const_seq_with_len [...] N`, indexed with
`Seq.index` (see `test/global_array_tactic`).

Because a pure global is immutable, writing it is rejected (C11 6.5.16p2),
and `_live(g)` is meaningless. If the storage itself is needed — to pass `&g`
to a function that asks for ownership of it — `acquire_var_g ()` hands out an
existentially quantified fraction: reads typecheck, writes (which need `1.0R`)
do not, and it can be acquired any number of times. It is an axiom (the
fraction is part of the one reserved for the global at program start), and it
is never applied automatically:

```c
_ghost_stmt(Global_g.acquire_var_g ());
```

Release it with `drop_` once done. `extern const T g;` without a definition is
a declaration of an object that lives elsewhere, so no value is assumed:
`var_g` is an `assume val`. See `test/addr_global/addr_global.c` and
`test/global_purity`.

### Mutable globals: bring your own permission

A mutable global has no pure value — its contents change — so PAL emits *only*
its address, and no ownership of it. There is deliberately no `acquire`:
handing out ownership of writable storage for free would let two callers each
take full permission and race. Instead the global behaves exactly like a
pointer parameter whose permission the caller supplies — **bring your own
permission**. Every function that touches `g` names the permission in its
contract with `_live(g)`:

```c
uint32_t counter;

void bump(void)
    _requires(_live(counter)) _requires(counter < 100)
    _ensures(_live(counter)) _ensures(counter == _old(counter) + 1)
{
    counter = counter + 1;
}
```

lowers to

```
fn func_bump () (#gval_counter: erased UInt32.t)
  requires uint32_t_pts_to addr_var_counter 1.0R gval_counter
  requires pure (UInt32.v (reveal gval_counter) < 100)
  ensures  exists* (gval_counter': UInt32.t).
             uint32_t_pts_to addr_var_counter 1.0R gval_counter' **
             pure (UInt32.v gval_counter' == UInt32.v (reveal gval_counter) + 1)
```

In spec position `g` reads as the contract's value `gval_g`, and `_old(g)` as
its pre-state value. Ownership threads through calls like any other: a caller
holding `_live(g)` hands it to the callee and gets it back.

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
  fails to verify for want of the points-to, exactly as for a pointer parameter.
- An initializer on a mutable global is ignored; what the storage holds is
  whatever the supplied permission says it holds. State it in a `_requires` if
  a function depends on it.
- `&g` *is* `addr_var_g`, so writing through a pointer to `g` while holding
  `_live(g)` works.

A mutable **array** global (`T g[N]`, `extern T g[]`) works the same way, with
`_live(g)` standing for the array's ownership:
`array_pts_to T_repr <size> (SizeT.v T_alignof) addr_var_g 1.0R gval_g`. When
`N` is known, `gval_g` is a `s: Seq.seq T { Seq.length s == N }`, so `g[N-1]`
needs no bounds precondition; otherwise state `i < g._length` as for an array
parameter.

See `test/global_mutable/global_mutable.c`,
`test/global_mutable_array/global_mutable_array.c`, and
`test/global_non_const_addr/global_non_const_addr.c` for the address-identity
side.

## See also

- `palow.md` — the memory model: how structs, unions, arrays and pointers are represented.
- `doc/skill.md` — a guide to writing specifications and proofs with PAL.
- `src/pass/emit_palow.rs` — the authoritative lowering when in doubt.
