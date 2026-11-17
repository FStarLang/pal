#include "pal.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* A field nested in the target of an owned pointer, `&p->ctx->sh.lead.seq`,
   lent to a call: the ownership the pointer is read out of is scattered, the
   target focused down to the field for the call, and both put back after. */

struct seq {
    uint64_t v;
};

struct hdr {
    uint32_t size;
    struct seq seq;
};

struct shc {
    bool has;
    struct hdr lead;
};

struct ctx {
    uint32_t count;
    struct shc sh;
};

struct params {
    struct ctx *ctx;
    uint32_t x;
};

struct header {
    uint64_t opaque;
    uint32_t status;
};

union _overlay req {
    _owning struct params params;
    struct header header;
};

uint64_t read_seq(const struct seq *s)
    _ensures(return == s->v)
{
    return s->v;
}

void set_seq(struct seq *s, uint64_t v)
    _ensures(s->v == v)
{
    s->v = v;
}

uint64_t read_through_struct(struct params *p)
    _ensures(return == p->ctx->sh.lead.seq.v)
{
    return read_seq(&p->ctx->sh.lead.seq);
}

uint64_t set_through_struct(struct params *p, uint64_t v)
    _ensures(return == v)
{
    set_seq(&p->ctx->sh.lead.seq, v);
    return p->ctx->sh.lead.seq.v;
}

uint64_t read_through_union(union req *r)
{
    return read_seq(&r->params.ctx->sh.lead.seq);
}

uint64_t set_through_union(union req *r, uint64_t v)
    _ensures(return == v)
{
    set_seq(&r->params.ctx->sh.lead.seq, v);
    return r->params.ctx->sh.lead.seq.v;
}

/* The rest of the target is left alone by the lend. */
uint32_t count_kept(struct params *p, uint64_t v)
    _ensures(return == _old(p->ctx->count))
{
    set_seq(&p->ctx->sh.lead.seq, v);
    return p->ctx->count;
}

/* Through a getter's alias: `h` names a place that reads `ctx`, so each use
   of it first checks that `ctx` has not moved -- a check that opens the
   ownership `ctx` is read out of, which the lend then opens again. */
struct hdr *get_lead(union req *r)
    _ensures(r->params.ctx == _old(r->params.ctx))
    _ensures(return == &r->params.ctx->sh.lead);

uint64_t read_through_getter(union req *r)
{
    struct hdr *h = get_lead(r);
    return read_seq(&h->seq);
}

struct hdr *get_lead_maybe(union req *r)
    _ensures(r->params.ctx == _old(r->params.ctx))
    _ensures(return == NULL || return == &r->params.ctx->sh.lead)
    _ensures(r->params.ctx->sh.has == _old(r->params.ctx->sh.has))
    _ensures(r->params.ctx->sh.has ==> return != NULL);

uint64_t read_maybe(union req *r)
{
    uint64_t x = 0;
    struct hdr *h = get_lead_maybe(r);
    if (h != NULL)
    {
        x = read_seq(&h->seq);
    }
    return x;
}

uint64_t read_asserted(union req *r)
    _requires(r->params.ctx->sh.has)
{
    uint64_t x = 0;
    struct hdr *h = get_lead_maybe(r);
    _assert(h != NULL);
    x = read_seq(&h->seq);
    return x;
}
