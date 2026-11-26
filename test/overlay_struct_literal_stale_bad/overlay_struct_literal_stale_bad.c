#include "pal.h"
#include <stdint.h>

/* A literal leaves the bytes of an overlay union outside the member it
   initializes unspecified (C11 6.2.6.1p7): here `p.hi`. Splitting the store
   into one to `a` alone would keep the old `hi`, and the assertions would
   verify although gcc stores 0 there. */

struct pair { uint32_t lo; uint32_t hi; };
union _overlay u { uint32_t a; struct pair p; };
struct s1 { union u x; uint32_t n; };
struct s2 { uint32_t n; union u x; };

void explicit_arm(struct s1 *p)
{
    p->x.p.lo = 0;
    p->x.p.hi = 7;
    *p = (struct s1){ .x = { .a = 1 }, .n = 2 };
    _assert(p->x.p.hi == 7);
}

void omitted_union(struct s2 *p)
{
    p->x.p.lo = 0;
    p->x.p.hi = 7;
    *p = (struct s2){ .n = 2 };
    _assert(p->x.p.hi == 7);
}
