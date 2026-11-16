#include "pal.h"
#include <stdint.h>
#include <stddef.h>

typedef struct _refine(this.bits._active) ctx {
    uint32_t n;
    union {
        uint64_t bits;
        uint8_t storage[8];
    };
} ctx;

uint64_t get_bits(ctx *c)
    _requires(c != NULL)
{
    return c->bits;
}

void set_bits(ctx *c, uint64_t b)
    _requires(c != NULL)
    _ensures(c->bits == b)
{
    c->bits = b;
}
