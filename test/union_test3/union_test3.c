#include "pal.h"
#include <stdint.h>

/*
 * Partial sub-field write to a (possibly non-active) union arm.
 *
 * Assigning through a union member — including a *single sub-field* of a
 * struct-typed arm, e.g. `u->x.a = v` — makes that arm the active member of
 * the union (C17 6.2.6.1p7 / 6.5.2.3). The *other* sub-fields of the arm then
 * hold unspecified (uninitialized) values; only the written sub-field can be
 * read straight back.
 *
 * PAL lowers `u->x.a` through the per-arm getter `union_u2__get_x`, whose
 * precondition requires arm `x` to be *already* active. Activation is done
 * explicitly by the user with `_ghost_stmt($activate(union u2::x) $(u))`,
 * which sets the arm tag and leaves the arm payload *uninitialized*. A
 * following `$unfold-uninit` exposes the per-field uninitialized cells so the
 * write can initialize just `a`; `b` stays uninitialized. The final per-field
 * initialization state is stated manually in `_ensures`.
 *
 * `build_full` shows the complementary case: writing *both* sub-fields fully
 * initializes the arm, so it can be re-folded back into a complete `union u2`
 * value. The re-fold happens automatically (the per-arm/-field fold lemmas are
 * `pulse_intro`), driven by the postcondition. Because the arm is complete at
 * exit, no annotations are needed — the default parameter mode's implicit
 * round-trip (`exists* v. pts_to u v`) is re-established.
 */

struct inner {
    int a;
    int b;
};

union u2 {
    struct inner x;
    int y;
};

/*
 * The two models say the same thing here in different words. The current one
 * owns each field through its own reference, so a half-written arm is one
 * `pts_to` and one `pts_to_uninit` on two references reached from the union.
 * Palow addresses a field as base+offset, so the same state is the two cells
 * at those offsets, plus the arm's padding and the bytes of the union that
 * the arm does not cover (`union_u2_rest_x`). That last conjunct has no
 * counterpart in the current model, which has nothing to say about the bytes
 * outside the live member; it is the price of the byte-level view, and the
 * reason the two spellings cannot be shared.
 */
#ifdef PALOW
int write_subfield(union u2 *u _consumes, int v)
    _ensures(_inline_pulse(
        exists* a_val.
          (int32_t_pts_to ($(u) +! Struct_inner.struct_inner_offsetof_a) 1.0R a_val **
           int32_t_pts_to_uninit ($(u) +! Struct_inner.struct_inner_offsetof_b) **
           Struct_inner.struct_inner_padding $(u) 1.0R **
           Union_u2.union_u2_rest_x $(u) 1.0R)))
    _ensures(return == v)
#else
int write_subfield(union u2 *u _consumes, int v)
    _ensures(_inline_pulse(
        exists* a_val.
          (Union_u2.union_u2__aux_raw_unfolded_x $(u) 1.0R **
           Struct_inner.struct_inner__aux_raw_unfolded (Union_u2.union_u2__x $(u)) 1.0R **
           Pulse.Lib.Reference.pts_to (Struct_inner.struct_inner__a_1 (Union_u2.union_u2__x $(u))) #1.0R a_val **
           Pulse.Lib.Reference.pts_to_uninit (Struct_inner.struct_inner__b_1 (Union_u2.union_u2__x $(u))))))
    _ensures(return == v)
#endif
{
    _ghost_stmt($activate(union u2::x) $(u));
    _ghost_stmt($unfold-uninit(struct inner) $&(u->x));
    u->x.a = v;
    return u->x.a;
}

void build_full(union u2 *u, int v1, int v2)
{
    _ghost_stmt($activate(union u2::x) $(u));
    _ghost_stmt($unfold-uninit(struct inner) $&(u->x));
    u->x.a = v1;
    u->x.b = v2;
}
