#pragma once
#include <stdint.h>

struct shape {
#ifdef WIDE_PREFIX
    uint64_t n;
#else
    uint32_t n;
#endif
    union { uint32_t a; uint64_t b; };
    union { uint32_t x; uint64_t y; } payload;
};
