#include "pal.h"
#include <stdint.h>

/* Ownership through an overlay union: `params` is `_owning`, so a pointer to
   the union carries what `params.ctx` points to. It is keyed on the bytes of
   `ctx`, so it survives reads and writes through `header` that miss them. */

struct ctx {
    uint32_t count;
};

struct pair {
    uint32_t lo;
    uint32_t hi;
};

struct params {
    struct ctx *ctx;
    uint32_t seq;
    struct pair last;
};

struct header {
    uint64_t opaque;
    uint32_t status;
    uint32_t flags;
};

/* The other members' layer sees the whole object as an overlay union of its
   own, as BOSS's requests do. */
union _overlay base {
    struct header header;
};

union _overlay req {
    _owning struct params params;
    struct header header;
    union base base;
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

/* A struct-typed field of the owning member is stored through a focus on it,
   and its view says `ctx` is still there. */
uint32_t set_last(union req *r, struct pair *v)
    _requires(r->params._active)
{
    r->params.last = *v;
    return r->params.ctx->count;
}

/* A callee handed the other member promises the bytes `ctx` is in back
   unchanged, so the ownership is still there after the call. */
void set_flags(union base *b, uint32_t f)
    _ensures(_unchanged(b->header.opaque))
{
    b->header.flags = f;
}

uint32_t call_then_count(union req *r, uint32_t f)
{
    set_flags(&r->base, f);
    return r->params.ctx->count;
}

/* A read-only callee leaves the union, and the ownership, as they were. */
uint32_t get_flags(const union base *b);

uint32_t peek_flags(const union req *r)
{
    return get_flags(&r->base);
}

uint32_t peek_then_count(union req *r)
{
    uint32_t f = get_flags(&r->base);
    return f + r->params.ctx->count;
}

void peek_only(union req *r)
{
    get_flags(&r->base);
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
