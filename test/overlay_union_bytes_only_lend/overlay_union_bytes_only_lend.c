#include "pal.h"
#include <stdint.h>

/* A `_plain` parameter whose contract gives only the union's bytes holds no
   ownership through the `_owning` member, so lending another member to a
   callee has no ownership to carry across the call: the callee's write lands
   in bytes the caller holds, and nothing else is asked of it. */

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

void set_flags(struct header *h, uint32_t f)
{
    h->flags = f;
}

void lend_bytes(_plain union req *r, uint32_t f)
    _preserves((_slprop)_inline_pulse(exists* v. Union_req.union_req_pts_to $(r) 1.0R v **
                                      pure (Union_req.union_req_is_header v)))
{
    set_flags(&r->header, f);
    set_flags(&r->header, f);
}
