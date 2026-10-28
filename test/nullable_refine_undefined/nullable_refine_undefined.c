#include "pal.h"
#include <stddef.h>
#include <stdint.h>

void undefined_optional_refinement(
    uint32_t divisor,
    _nullable _out _refine(*this == 0u / divisor || *this != 0u / divisor) uint32_t *p)
    _requires(divisor == 0)
{
    if (p != NULL) {
        *p = 0;
    }
}
