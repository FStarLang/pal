#include "pal.h"
#include <stdint.h>
#include <stddef.h>

typedef struct _refine(this.bits._active) ctx {
    uint32_t n;
    union {
        uint64_t bits;
        uint32_t half;
    };
} ctx;

uint32_t get_n(ctx *c)
    _requires(c != NULL)
{
    return c->n;
}

// The `half` member is the live one, so `c` does not satisfy its type's
// refinement.
uint32_t from_storage(void)
{
    ctx c = { .n = 0, .half = 0 };
    return get_n(&c);
}
