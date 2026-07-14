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
 */

struct inner {
    int a;
    int b;
};

union u2 {
    struct inner x;
    int y;
};

int write_subfield(union u2 *u _consumes, int v)
    _ensures(_inline_pulse(
        exists* a_val.
          (Union_u2.union_u2__aux_raw_unfolded_x $(u) 1.0R **
           Struct_inner.struct_inner__aux_raw_unfolded (Union_u2.union_u2__x $(u)) 1.0R **
           Pulse.Lib.Reference.pts_to (Struct_inner.struct_inner__a_1 (Union_u2.union_u2__x $(u))) #1.0R a_val **
           Pulse.Lib.Reference.pts_to_uninit (Struct_inner.struct_inner__b_1 (Union_u2.union_u2__x $(u))))))
    _ensures(return == v)
{
    _ghost_stmt($activate(union u2::x) $(u));
    _ghost_stmt($unfold-uninit(struct inner) $&(u->x));
    u->x.a = v;
    return u->x.a;
}
