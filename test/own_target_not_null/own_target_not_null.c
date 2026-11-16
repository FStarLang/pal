#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* What an owned pointer reaches is a points-to of its own, so the pointer is
   not null, and neither is the address of a field of its target. */

struct inner {
    uint32_t a;
};

struct ctx {
    uint32_t has;
    struct inner in;
};

struct req {
    struct ctx *c;
    uint32_t k;
};

struct inner *get_lead(struct req *r)
    _ensures(r->c == _old(r->c))
    _ensures(return == NULL || return == &r->c->in)
    _ensures(r->c->has != 0 ==> return != NULL)
{
    struct inner *q = NULL;
    if (r->c->has != 0)
    {
        q = &r->c->in;
    }
    return q;
}

struct inner *get_in(struct req *r)
    _ensures(r->c == _old(r->c))
    _ensures(return == &r->c->in)
    _ensures(return != NULL)
{
    uint32_t h = r->c->has;
    (void)h;
    return &r->c->in;
}

/* The field at offset zero has no such fact of its own (an array); a later
   field does, and it shares the struct's provenance. */
struct ctx2 {
    uint8_t pad[8];
    uint32_t has;
    struct inner in;
};

struct req2 {
    struct ctx2 *c;
};

struct inner *get_in2(struct req2 *r)
    _ensures(r->c == _old(r->c))
    _ensures(return != NULL)
{
    uint32_t h = r->c->has;
    (void)h;
    return &r->c->in;
}
