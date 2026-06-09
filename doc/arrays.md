This doc explains how arrays are modelled in PAL. The core Pulse library lives in `pulse/Pulse.Lib.C.Array.fsti`; PAL targets it from `src/pass/emit.rs`.

## Three layers of representation

1. `array t` — the runtime handle. Carries no contents; only identity, base, offset, and length. This is the type you actually pass to functions.
2. `array_spec t` — the ghost contents. A per-slot record of (a) whether the slot is *initialized*, (b) whether the slot is *masked* (allocated but uninitialized), and (c) the slot's value when initialized. Helpers: `array_spec_len`, `array_spec_initd`, `array_spec_mask`, `array_spec_idx`, `array_spec_upd`.
3. `full_array_spec t = s: array_spec t { array_spec_full s }` — refinement of `array_spec t` where every slot is initialized. This is the "fully initialized" shape PAL uses by default.

## Three points-to flavors

1. `array_pts_to a p s` — `a` has permission `p` to contents `s: array_spec t`. The most general form; allows partially-initialized arrays.
2. `array_pts_to_full a p s` — sugar for `array_pts_to a p s` with `s: full_array_spec t`. PAL emits this in pre/post-conditions of functions taking `_array T*` parameters.
3. `array_pts_to_uninit' a` — the array is allocated but every slot is uninitialized. Used in the `aux_raw_*_uninit` lemmas for inline-array struct/union fields and as the post-condition of `stack_alloc_array`.

## Read vs write — stateful and ghost

| operation       | signature                                                                                   | notes                                |
|-----------------|---------------------------------------------------------------------------------------------|--------------------------------------|
| `array_read`    | `array t -> SZ.t -> stt t (array_pts_to a p s) (...)`                                       | stateful; requires `array_pts_to`     |
| `array_write`   | `array t -> SZ.t -> t -> stt unit (array_pts_to a 1.0R s) (...)`                            | stateful; full permission             |
| `array_spec_idx`| `array_spec t -> (i: nat { array_spec_initd s i }) -> GTot t`                               | ghost; takes `nat`, not `SZ.t`        |
| `array_spec_upd`| `array_spec t -> nat -> t -> array_spec t`                                                  | ghost                                 |
| `length_of`     | `array t -> ghost nat` (rewrites to `array_spec_len y`)                                     | ghost length projection               |

PAL emits the `SZ.t`-indexed forms by default (subscripts come out as `0sz`, `1sz`, …). When a subscript appears in a *spec* context (an `_ensures` clause), PAL inserts `SizeT.v` and uses `array_spec_idx`.

## PAL surface

| C / PAL syntax              | meaning                                                              |
|-----------------------------|----------------------------------------------------------------------|
| `T a[]` (parameter)         | implicit `_array`; lowers to `(var_a: array T)`                      |
| `_array T *a` (parameter)   | same as above                                                        |
| `_arrayptr T *a`            | sub-array pointer: same `array T` type, related by `arrayptr_pts_to` |
| `T a[N]` (struct field)     | inline array; stored as `full_array_spec T { len == N }` in the noeq (see `structs.md`) |
| `a._length`                 | lowers to `length_of a`                                              |
| `a[i]` (rvalue)             | `array_read a i`                                                     |
| `a[i] = v`                  | `array_write a i v` (peephole on `StmtT::Assign`)                    |

`_array` and `_arrayptr` annotations are defined in `pal.h`; absent them, `T*` is treated as a single-element reference (`ref T`).

## Generated function signature

For `void foo(_array unsigned *a) _requires(a._length == 2) ...`, PAL emits in `Func_foo.fsti`:

```
fn func_foo (var_a: (array UInt32.t))
  requires exists* (val_a_0: (full_array_spec UInt32.t)). array_pts_to_full var_a 1.0R val_a_0
  requires (with_pure ((reveal (length_of var_a)) = 2))
  ...
```

The `exists*`-bound `val_a_0` is the framed array contents; user-written `_requires`/`_ensures` are wrapped in `with_pure` and reference `array_read` for in-bounds initialised slots.

## Inline-array struct/union fields (cross-reference)

Inline arrays embedded in structs/unions have a *dual* representation: the noeq record stores the contents (`full_array_spec T { len == N }`) by value, and a separate axiomatized ghost projection (`struct_foo__b_1`) returns the array *handle* (`array T { length a == N }`). They are tied together by `array_pts_to` (not `array_pts_to_full`) in `aux_raw_unfold`/`aux_raw_fold`. See `structs.md` for the full picture.

## Arrayptrs

`_arrayptr T*` denotes a sub-array sharing a base with its parent array. The Pulse representation is just an `array t` with `length == 0`; the relationship to the parent is asserted by the pure `arrayptr_pts_to` slprop. Pointer arithmetic (`a + i`) lowers to `arrayptr_shift`; comparisons lower to `arrayptr_eq` / `arrayptr_lt` / `arrayptr_lte`.
