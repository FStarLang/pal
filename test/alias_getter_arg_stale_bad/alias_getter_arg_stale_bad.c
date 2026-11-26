#include "pal.h"
#include <stdint.h>

/* Binding `q2` by a getter is not a use of `q2`, but the call still reads its
   arguments: `*q1` is the `a` of the context `r->c` held when `q1` was set,
   which `swap` may since have replaced. Read as `r->c->in.a`, it would let
   the assertion below verify although it is false in C. */

struct inner { uint32_t a; uint32_t b; };
struct ctx { struct inner in; uint32_t n; };
struct req { struct ctx *c; uint32_t k; };

struct inner *get_in(struct ctx *o, uint32_t v)
    _ensures(return == &o->in)
    _ensures(o->n == v);

void swap(struct req *r, struct req *g);

void stale_arg(struct req *r, struct req *g, struct ctx *o)
{
    uint32_t *q1 = &r->c->in.a;
    swap(r, g);
    struct inner *q2 = get_in(o, *q1);
    q2->b = 1;
    _assert(o->n == r->c->in.a);
}
