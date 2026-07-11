#include "pal.h"
#include <stdbool.h>

/*
 * Common initial sequence (CIS) casting — C17 6.5.2.3p6.
 *
 * If a union contains several structures that share a "common initial
 * sequence" (one or more leading members with compatible types), then it is
 * permitted to inspect the common initial part of any of them through any of
 * the arms, anywhere that the union is visible. For a struct-typed member to
 * be part of the CIS it must be the SAME struct type in every arm.
 *
 * Anonymous members (6.7.2.1p13) are "hoisted": their members are accessed
 * directly on the enclosing union.
 *
 * PAL implements the CIS rule (C17 6.5.2.3p6): for the leading run of members
 * shared by every arm (same name and compatible type), cross-arm reads and
 * writes are lowered to arm-agnostic accessors so they verify WITHOUT any
 * `_active` annotation. Writing a CIS member preserves the active arm and only
 * updates that member. This test verifies green.
 */

/* Struct-typed CIS member: same struct type in every arm. */
struct point {
    int x;
    int y;
};

/* ---- Example 1: three NAMED arms, CIS { int tag; struct point pt } ---- */

struct as_int {
    int tag;
    struct point pt;
    int payload;
};

struct as_bool {
    int tag;
    struct point pt;
    _Bool payload;
};

struct as_char {
    int tag;
    struct point pt;
    char payload;
};

union variant {
    struct as_int i;
    struct as_bool b;
    struct as_char c;
};

/* cross-arm READ of a scalar CIS field: write through i, read through b. */
int cis_read(union variant *u, int t)
    _ensures(return == t)
{
    u->i.tag = t;
    return u->b.tag;
}

/* cross-arm READ of a STRUCT CIS sub-member: write i.pt.x, read c.pt.x. */
int cis_read_pt(union variant *u, int vx)
    _ensures(return == vx)
{
    u->i.pt.x = vx;
    return u->c.pt.x;
}

/* cross-arm WRITE: write the CIS field through b, observe it through i. */
int cis_write(union variant *u, int t)
    _ensures(return == t)
{
    u->i.tag = 0;
    u->b.tag = t;
    return u->i.tag;
}

/* ---- Example 2: one ANONYMOUS + two NAMED arms,
 *      longer CIS { int tag; short kind; struct point pt } ---- */

union variant_anon {
    struct {
        int tag;
        short kind;
        struct point pt;
        int px;
    };
    struct named1 {
        int tag;
        short kind;
        struct point pt;
        _Bool py;
    } n1;
    struct named2 {
        int tag;
        short kind;
        struct point pt;
        int pz;
    } n2;
};

/* cross-arm READ via the ANONYMOUS arm: write n1.tag, read the hoisted u->tag. */
int cis_read_anon(union variant_anon *u, int t)
    _ensures(return == t)
{
    u->n1.tag = t;
    return u->tag;
}

/* cross-arm WRITE of a STRUCT sub-member via the ANONYMOUS arm:
 * write the hoisted u->pt.y, read it back through n2. */
int cis_write_anon_pt(union variant_anon *u, int vy)
    _ensures(return == vy)
{
    u->pt.y = vy;
    return u->n2.pt.y;
}

/* cross-arm READ across two NAMED arms, short CIS field: write n1.kind,
 * read n2.kind. */
short cis_named_kind(union variant_anon *u, short k)
    _ensures(return == k)
{
    u->n1.kind = k;
    return u->n2.kind;
}

/* ---- Example 3: UNEQUAL-length arms — the CIS is bounded by the SHORTEST arm.
 *
 * `short_s` contributes only { tag }, so the union-wide common initial sequence
 * is { tag } even though `long_a` and `long_b` additionally share { extra }.
 * This checks PAL does NOT over-approximate: `extra` must NOT be treated as CIS
 * just because two of the three arms happen to share it. Only `tag` (common to
 * ALL arms) gets the arm-agnostic accessors.
 *
 * The positive `three_read_tag` below exercises the CIS member `tag` cross-arm
 * with no annotation. The negative case — reading `extra` cross-arm — is
 * correctly REJECTED (Error 19, `VC = Field_three__b? val_u`): `extra` is shared
 * only by `a` and `b`, not by the shorter `s`, so it is not in the union-wide
 * CIS and is only reachable through its own active arm. Because the harness
 * requires every emitted function to verify, that negative is documented rather
 * than kept as a (red) function, confirming PAL does not over-approximate.
 */

struct short_s {
    int tag;
};

struct long_a {
    int tag;
    int extra;
    int a_only;
};

struct long_b {
    int tag;
    int extra;
    int b_only;
};

union three {
    struct short_s s;
    struct long_a a;
    struct long_b b;
};

/* `tag` is the 3-arm CIS: cross-arm write via `a`, read via `b`, NO annotation. */
int three_read_tag(union three *u, int t)
    _ensures(return == t)
{
    u->a.tag = t;
    return u->b.tag;
}
