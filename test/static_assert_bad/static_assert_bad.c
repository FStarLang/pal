#include "pal.h"

unsigned failed_static_assert(unsigned x) {
#ifdef C2PULSE
    // This diagnostic test intentionally fails Clang validation during PAL
    // translation; omit the invalid assertion for the native compilation check.
    _Static_assert(0, "block-scope assertion must fail");
#endif
    return x;
}
