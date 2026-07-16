#include "pal.h"
#include <stdint.h>

/*
 * Common Initial Sequence (CIS), simplest case.
 *
 * A union with two arms whose members have EXACTLY IDENTICAL fields (same
 * names, same types): one anonymous struct and one named struct. Because every
 * corresponding member has an identical name and type, the two arms share their
 * whole sequence as a common initial sequence, so — per C17 6.5.2.3p6 — after
 * fully building one arm we may inspect (or update) the corresponding member of
 * the other arm.
 *
 * Each function first FULLY builds one arm with a whole-union compound literal,
 * then performs a cross-arm CIS access through the *other* arm. The functions
 * below exercise every combination of {read, write} x {named branch, unnamed
 * (promoted) branch}. Because the two arms are byte-for-byte identical, a CIS
 * write is modelled as an in-place update of the shared member that preserves
 * whichever arm is active, so the value reads back consistently through either
 * branch.
 */

struct named {
    int p0;
    int p1;
};

union u {
    struct {        /* anonymous arm; promotes p0, p1 into the union */
        int p0;
        int p1;
    };
    struct named n;
};

/* READ via the NAMED branch: build the anonymous arm, read the named member. */
int cis_read_via_named(union u *u, int t)
    _ensures(return == t)
{
    *u = (union u){ .p0 = 0, .p1 = t };
    return u->n.p1;
}

/* READ via the UNNAMED branch: build the named arm, read the promoted member. */
int cis_read_via_unnamed(union u *u, int t)
    _ensures(return == t)
{
    *u = (union u){ .n = { .p0 = 0, .p1 = t } };
    return u->p1;
}

/* WRITE via the NAMED branch: build the anonymous arm, write through the named
 * member, then read the value back through the unnamed branch. */
int cis_write_via_named(union u *u, int t)
    _ensures(return == t)
{
    *u = (union u){ .p0 = 0, .p1 = 0 };
    u->n.p1 = t;
    return u->p1;
}

/* WRITE via the UNNAMED branch: build the named arm, write through the promoted
 * member, then read the value back through the named branch. */
int cis_write_via_unnamed(union u *u, int t)
    _ensures(return == t)
{
    *u = (union u){ .n = { .p0 = 0, .p1 = 0 } };
    u->p1 = t;
    return u->n.p1;
}

/* Arm ORDER independence: same union but with the named struct first and the
 * anonymous struct second. Build the named arm, read the promoted member. */
union u2 {
    struct named n;
    struct {        /* anonymous arm; promotes p0, p1 into the union */
        int p0;
        int p1;
    };
};

int cis_read_reordered(union u2 *u, int t)
    _ensures(return == t)
{
    *u = (union u2){ .n = { .p0 = 0, .p1 = t } };
    return u->p1;
}
