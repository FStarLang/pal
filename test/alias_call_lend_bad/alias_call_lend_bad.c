#include "pal.h"
#include <stdint.h>

/* Once `swap` may have moved `r->c`, `q` still addresses the old context,
   so lending `q` cannot be read as lending `&r->c->in`. */

struct inner { uint32_t a; uint32_t b; };
struct ctx { struct inner in; uint32_t n; };
struct req { struct ctx *c; uint32_t k; };

struct inner *get_deep(struct req *r)
    _ensures(return == &r->c->in)
{
    return &r->c->in;
}

void swap(struct req *r);

void set_a(struct inner *i, uint32_t v)
    _ensures(i->a == v);

void stale(struct req *r)
{
    struct inner *q = get_deep(r);
    swap(r);
    set_a(q, 3);
}
