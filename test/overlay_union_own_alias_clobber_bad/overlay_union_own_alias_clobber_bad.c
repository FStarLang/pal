#include "pal.h"
#include <stdint.h>

/* As in `overlay_union_own_clobber_bad`, but the store reaches `opaque`
   through a getter macro's pointer to the other member: following the alias
   must not make the bytes `params.ctx` is in look untouched. */

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

#define header_of(r) (&(r)->header)

uint32_t clobber(union req *r)
{
    struct header *h;
    h = header_of(r);
    h->opaque = 0;
    return r->params.ctx->count;
}
