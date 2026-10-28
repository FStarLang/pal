#include "pal.h"
#include <stdint.h>

struct pair {
    uint32_t first;
    uint32_t last;
};

union choice {
    uint32_t scalar;
    struct pair pair;
};

uint32_t read_value(const uint32_t *p)
    _ensures(return == *p)
{
    return *p;
}

uint32_t inactive_tail(union choice *u)
    _requires(u->scalar._active)
{
    // The scalar covers only the first field, not the tail being read.
    return read_value(&u->pair.last);
}
