#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

/* A callee that may store through the lent arm can change it, so its value
   is not known to be what it was. */

struct bitmap {
    uint64_t count;
    uint64_t bits[];
};

void set(struct bitmap *b, uint64_t i);

struct ctx {
    uint32_t k;
    union {
        struct bitmap bm;
        uint8_t storage[32];
    };
};

void update(struct ctx *c, uint64_t i)
    _requires(c->bm._active)
    _ensures(c->bm._active)
    _ensures(c->bm.count == _old(c->bm.count))
{
    set(&c->bm, i);
}
