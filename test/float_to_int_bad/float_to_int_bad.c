#include "pal.h"
#include <stdint.h>

// An arbitrary double need not fit in an int32_t: the conversion is undefined
// for NaN, the infinities and anything outside (-2^31 - 1, 2^31), so it has to
// be rejected.
int32_t double_to_int32(double d) {
    return (int32_t) d;
}
