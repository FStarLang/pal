#include "pal.h"
#include <stdint.h>

/* `_owning` marks the one member of an `_overlay` union whose pointers own
   what they point at. Anywhere else it is reported rather than ignored. */

struct ctx {
    uint32_t count;
};

struct params {
    struct ctx *ctx;
    uint32_t seq;
};

struct holder {
    _owning struct params params;
};

union tagged {
    _owning struct params params;
    uint64_t raw;
};

union _overlay two {
    _owning struct params a;
    _owning struct params b;
};

union _overlay scalar {
    _owning uint64_t raw;
    struct params params;
};

uint32_t use(struct holder *h, union tagged *t, union two *w, union scalar *s)
{
    return 0;
}
