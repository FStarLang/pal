#include "pal.h"
#include <stdint.h>
#undef assert

struct context { uint32_t first; uint32_t count; };
struct params { struct context *ctx; };
union _overlay request { _owning struct params params; uintptr_t payload; };
typedef _plain union request request_bytes;

const uint32_t *count_address(const request_bytes *r)
    _requires(_inline_pulse(pure (Union_request.union_request_own_ok $(*r))))
    _ensures(return == &r->params.ctx->count)
{
    return &r->params.ctx->count;
}

uint32_t read_count(const union request *r)
    _ensures(return == r->params.ctx->count)
{
    _ghost_stmt(with v s. assert (union_request_own v _ s);
                union_request_own_scatter v;
                union_request_own_gather v);
    const uint32_t *p = count_address(r);
    return *p;
}

uint32_t read_without_context(const request_bytes *r)
    _requires(_inline_pulse(pure (Union_request.union_request_own_ok $(*r))))
{
    const uint32_t *p = count_address(r);
    return *p;
}

static void clear_word(_plain uint32_t *p)
    _requires(_inline_pulse(uint32_t_pts_to $(p) 1.0R 1ul))
    _ensures(_inline_pulse(uint32_t_pts_to $(p) 1.0R 0ul))
{
    *p = 0;
}

void clear_count(const request_bytes *r)
    _requires(_inline_pulse(pure (Union_request.union_request_own_ok $(*r))))
    _requires(_inline_pulse(uint32_t_pts_to
        (Pulse.Lib.C.Palow.Overlay.ptr_of_bytes (Pulse.Lib.C.Palow.Bytes.slice $(*r) 0 8)
         +! Struct_context.struct_context_offsetof_count) 1.0R 1ul))
    _ensures(_inline_pulse(uint32_t_pts_to
        (Pulse.Lib.C.Palow.Overlay.ptr_of_bytes (Pulse.Lib.C.Palow.Bytes.slice $(*r) 0 8)
         +! Struct_context.struct_context_offsetof_count) 1.0R 0ul))
{
    clear_word(&r->params.ctx->count);
}
