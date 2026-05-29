// Test: Unary negation on unsigned types
//
// The C standard defines -x on unsigned types as producing a valid
// unsigned result (2^N - x).

#include "pal.h"
#include <stdint.h>

int neg_u32(uint32_t x) {
    return -x;
}

int64_t neg_u64(uint64_t x) {
    return -x;
}
