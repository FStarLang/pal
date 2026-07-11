#include "pal.h"
#include <stdint.h>

/*
 * Partial sub-field write to a (possibly non-active) union arm.
 *
 * This is NOT about the common-initial-sequence rule (see test/union_cis);
 * it is a general property of C union member access: assigning through a
 * union member — including a *single sub-field* of a struct-typed arm, e.g.
 * `u->x.a = v` — makes that arm the active member of the union (C17
 * 6.2.6.1p7 / 6.5.2.3). The other sub-fields of the arm then hold unspecified
 * values, but the written sub-field can be read straight back.
 *
 * PAL currently lowers `u->x.a` through the per-arm getter `union_u2__get_x`,
 * whose precondition requires arm `x` to be *already* active. At function
 * entry the active arm is unknown, so a partial sub-field write like the one
 * below fails to verify (Error 19, `VC = Field_u2__x? val_u`). The write
 * should instead ACTIVATE arm `x` first.
 */

struct inner {
    int a;
    int b;
};

union u2 {
    struct inner x;
    int y;
};

/* Writing `u->x.a` should activate arm `x`; reading it back must return `v`. */
int write_subfield(union u2 *u, int v)
    _ensures(return == v)
{
    u->x.a = v;
    return u->x.a;
}
