#include "pal.h"
#include <stdint.h>

/* The lent field is what the callee writes: its old value is gone. */

struct seq {
    uint64_t v;
};

struct ctx {
    uint32_t count;
    struct seq seq;
};

struct params {
    struct ctx *ctx;
};

void bump_seq(struct seq *s)
{
    s->v = s->v + 1;
}

uint64_t stale(struct params *p)
    _ensures(return == _old(p->ctx->seq.v))
{
    bump_seq(&p->ctx->seq);
    return p->ctx->seq.v;
}
