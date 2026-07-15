#include "pal.h"
#include <stdint.h>

/*
 * Common Initial Sequence (CIS) with DIFFERENT member names.
 *
 * C17 6.5.2.3p6: if a union contains several structures that share a "common
 * initial sequence", and the union object currently contains one of them, it
 * is permitted to inspect the common initial part of any of them. Two structs
 * share a common initial sequence for a run of one or more initial members if
 * corresponding members have COMPATIBLE TYPES (and, for bit-fields, the same
 * widths) — the member *names need NOT match*.
 *
 * To keep these examples about the CIS rule alone — and NOT about partially
 * initialized unions — every function first FULLY constructs one arm with a
 * whole-union compound literal (see `build_full` in union_test3 for the
 * underlying lesson: writing every sub-field initializes the whole arm, which
 * folds back into a complete union value with no leftover uninitialized cells).
 * Only after the arm is fully built do we perform the cross-arm CIS access.
 *
 * PAL currently lowers each union-arm sub-field access through a per-arm getter
 * that requires that exact arm to be the active member, and (on the union_cis
 * branch) only matches CIS members by *identical name*. Neither handles the
 * case below, where the corresponding CIS members have compatible `int` type
 * but different names (foo/bar vs baz/qux, m0/m1 vs n0/n1). These functions are
 * therefore expected to FAIL verification today; they document the target for a
 * future, position/type-based (name-independent) CIS extension.
 */

/* ---- Named struct arms with a multi-member, different-name CIS ---- */

struct arm_a {
    int foo;
    int bar;
    int a_only;
};

struct arm_b {
    int baz;      /* corresponds to foo: int vs int, different name */
    int qux;      /* corresponds to bar: int vs int, different name */
    long b_only;  /* CIS ends here: int a_only vs long b_only are not compatible */
};

union u {
    struct arm_a a;
    struct arm_b b;
};

/* cross-arm CIS READ of the FIRST CIS member: build arm a, read b.baz. */
int cis_read_first(union u *u, int t)
    _ensures(return == t)
{
    *u = (union u){ .a = { .foo = t, .bar = 0, .a_only = 0 } };
    return u->b.baz;
}

/* cross-arm CIS READ of a NON-FIRST CIS member: build arm a, read b.qux. */
int cis_read_nonfirst(union u *u, int t)
    _ensures(return == t)
{
    *u = (union u){ .a = { .foo = 0, .bar = t, .a_only = 0 } };
    return u->b.qux;
}

/* cross-arm CIS WRITE returning the WHOLE union: build arm a, then write the
 * first CIS member through arm b's differently-named member, and return *u. */
union u cis_write_diff_names(union u *u, int t)
{
    *u = (union u){ .a = { .foo = 0, .bar = 0, .a_only = 0 } };
    u->b.baz = t;
    return *u;
}

/* ---- Anonymous struct arms with a different-name CIS ---- */

union v {
    struct {
        int m0;
        int m1;
        int v_a_only;
    };
    struct {
        int n0;   /* corresponds to m0 */
        int n1;   /* corresponds to m1 */
        long v_b_only;
    };
};

/* cross-arm CIS READ through anonymous arms: build the first arm, read n1. */
int cis_anon_read(union v *u, int t)
    _ensures(return == t)
{
    *u = (union v){ .m0 = 0, .m1 = t, .v_a_only = 0 };
    return u->n1;
}

/* ---- Anonymous arm + named struct arms sharing the SAME CIS names ---- */

struct wn1 {
    int p0;
    int p1;
    int wn1_only;
};

struct wn2 {
    int p0;
    int p1;
    long wn2_only;  /* CIS ends here: int/int/long at position 2 disagree */
};

union w {
    struct {        /* anonymous arm; promotes p0, p1 into the union */
        int p0;
        int p1;
        int w_anon_only;
    };
    struct wn1 n1;
    struct wn2 n2;
};

/* cross-arm CIS READ mixing the ANONYMOUS arm with a NAMED arm. Here the
 * corresponding CIS members share the SAME names (p0/p1) across all arms — the
 * complement of `union v`, whose CIS members had different names. Build the
 * anonymous arm, then read the named arm's p1. */
int cis_anon_named_read(union w *u, int t)
    _ensures(return == t)
{
    *u = (union w){ .p0 = 0, .p1 = t, .w_anon_only = 0 };
    return u->n1.p1;
}

/* cross-arm CIS READ in the other direction: build a NAMED arm, then read the
 * ANONYMOUS arm's promoted member (u->p1). */
int cis_anon_unnamed_read(union w *u, int t)
    _ensures(return == t)
{
    *u = (union w){ .n1 = { .p0 = 0, .p1 = t, .wn1_only = 0 } };
    return u->p1;
}
