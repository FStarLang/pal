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

union _overlay req {
    _owning struct params params;
    struct header header;
};

uint32_t clobber(union req *r)
{
    r->header.opaque = 0;
    return r->params.ctx->count;
}
