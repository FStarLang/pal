#include "pal.h"
#include <stdint.h>

struct payload {
    int32_t value;
};

union choice {
    struct payload record;
    _Bool flag;
};

int32_t missing_tag(const union choice *p, uint32_t n)
    _requires(n > 0)
{
    return p->record.value;
}
