#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

/* The record is rebound, so what was known about it before the conditional
   is not known after it unless the `_ensures` says so. */

struct ctx {
    bool has;
    uint32_t v;
};

struct req {
    struct ctx *c;
    uint32_t n;
};

uint32_t get_v(struct req *r)
    _requires(r->c->has)
    _ensures(r->c == _old(r->c))
    _ensures(r->c->has)
    _ensures(return == r->c->v);

uint32_t pick(struct req *r, bool f)
    _requires(r->c->has)
{
    uint32_t x = 0;
    if (f)
        _ensures(_live(x))
    {
        x = get_v(r);
    }
    x = get_v(r);
    return x;
}
