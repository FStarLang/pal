This doc explains how structs are modelled in pal. Whenever you define a struct `foo`, PAL generates a file `Struct_foo.fst`. This file contains the following:

1. `noeq type struct_foo`: This is the F* record that is the lightweight representation of the struct.
2. `noeq type struct_foo__spec`: A collection of all the data that pointers in the struct point to. Marked `[@@erasable]` (ghost-only). If the struct has no pointer fields, this type — together with its `pred_unfold`/`pred_fold` ghost fns — is omitted and `struct_foo__pred` collapses to `emp`.
3. `struct_foo__pred` and `struct_foo__uninit_pred`: These contain the initialized and uninitialized versions of the points-tos linking the fields in `struct_foo` to the things that they point to in `struct_foo__spec`
4. `struct_foo__pred_unfold` : A ghost fn that given `struct_foo__pred` decomposes it into its constituent points-tos. It has the `[@@pulse_intro]` annotation, which tells pulse to apply it whenever it wants to prove one of the predicates included in its postcondition.
5. `struct_foo__pred_fold` : The fold version of the above ghost fn.
6. `struct_foo__aux_raw_unfolded`: An axiomatized function that denotes that the struct is currently unfolded.
7. `struct_foo__field_1` : An axiomatized function that takes a pointer to the structure and converts it to a pointer of `field`. The `1` is just for name mangling.
8. `struct_foo__aux_raw_unfold` : An axiomatized function that takes in a points-to to the struct and converts it to points-to for each field.
9. `struct_foo__aux_raw_fold` : The fold version of the above.
10. `struct_foo__aux_raw_fold_uninit` and `struct_foo__aux_raw_unfold_uninit` : uninit versions of the above.
11. `struct_foo__get_field`: A getter for the fields of the struct. Its precondition is that the struct must be in the unfolded state.
12. `has_zero_default_struct_foo` : A typeclass instance defining the default 0 values for the struct (according to the C standard).

Unions are emitted analogously to `Union_foo.fst`, with a sum-type constructor in place of the record.

## Examples

Tests exercising plain structs (without inline arrays):

- [`test/simple_struct/simple_struct.c`](../test/simple_struct/simple_struct.c),  [`test/struct/struct.c`](../test/struct/struct.c) — minimal struct.
- [`test/inner_struct/inner_struct.c`](../test/inner_struct/inner_struct.c) — nested struct fields.
- [`test/forward_struct/forward_struct.c`](../test/forward_struct/forward_struct.c) — forward declarations.
- [`test/recursive_struct/recursive_struct.c`](../test/recursive_struct/recursive_struct.c) — self-referential structs.
- [`test/swap_struct/swap_struct.c`](../test/swap_struct/swap_struct.c), [`test/swap_struct_fun/swap_struct_fun.c`](../test/swap_struct_fun/swap_struct_fun.c) — swapping struct fields by reference.
- [`test/eager_unfold_struct/eager_unfold_struct.c`](../test/eager_unfold_struct/eager_unfold_struct.c) — `_pulse_eager_unfold_predicate`.

Structs containing inline arrays (`T b[N]`) are exercised separately because their fields have a dual representation (see the inline-array notes above):

- [`test/struct_inline_array/struct_inline_array.c`](../test/struct_inline_array/struct_inline_array.c) — read and write inline-array fields by reference and by value.