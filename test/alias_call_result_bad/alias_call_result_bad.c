#include "pal.h"
#include <stdint.h>

/* The place a getter returns reads `r->c`. Once `swap` may have moved
   `r->c`, `q` still addresses the old context, so an access through `q`
   cannot be read as one through `r->c`. */

struct inner { uint32_t a; uint32_t b; };
struct ctx { struct inner in; uint32_t n; };
struct req { struct ctx *c; uint32_t k; };

struct inner *get_deep(struct req *r)
    _ensures(return == &r->c->in)
{
    return &r->c->in;
}

void swap(struct req *r);

void stale(struct req *r)
{
    struct inner *q = get_deep(r);
    swap(r);
    q->a = 3;
}
