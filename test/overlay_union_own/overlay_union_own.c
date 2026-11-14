#include "pal.h"
#include <stdint.h>

/* Ownership through an overlay union: `params` is `_owning`, so a pointer to
   the union carries what `params.ctx` points to. It is keyed on the bytes of
   `ctx`, so it survives reads and writes through `header` that miss them. */

struct ctx {
    uint32_t count;
};

struct params {
    struct ctx *ctx;
    uint32_t seq;
};

struct header {
    uint64_t opaque;
    uint32_t status;
    uint32_t flags;
};

union _overlay req {
    _owning struct params params;
    struct header header;
};

uint32_t get_count(union req *r)
{
    return r->params.ctx->count;
}

void bump(union req *r)
{
    r->params.ctx->count = r->params.ctx->count + 1;
}

/* Another member's bytes, and `seq`: none of them hold `ctx`. */
uint32_t flags_then_count(union req *r, uint32_t f)
{
    r->header.flags = f;
    r->header.status = 0;
    r->params.seq = 7;
    return r->params.ctx->count;
}

/* A read through the other member leaves everything as it was. */
uint32_t status_and_count(union req *r)
{
    r->header.status = 3;
    uint32_t s = r->header.status;
    return s + r->params.ctx->count;
}

/* The ownership is the caller's to pass on, and comes back. */
uint32_t twice(union req *r)
{
    uint32_t a = get_count(r);
    r->header.flags = a;
    bump(r);
    return get_count(r);
}

struct ctx *get_ctx(union req *r)
{
    return r->params.ctx;
}
