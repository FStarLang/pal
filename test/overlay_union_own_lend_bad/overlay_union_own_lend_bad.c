#include "pal.h"
#include <stdint.h>

/* `opaque` is the bytes `params.ctx` is in, so storing to it leaves the
   ownership `params` carries with the pointer that was there, and the load
   that follows finds nothing it may dereference. */

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

void set_flags(union base *b, uint32_t f)
{
    b->header.flags = f;
}

uint32_t call_clobber(union req *r, uint32_t f)
{
    set_flags(&r->base, f);
    return r->params.ctx->count;
}
