#include "pal.h"
#include <stddef.h>
#include <stdint.h>

void unguarded_other_refinement(
    _nullable _out int32_t *other,
    _nullable _out _refine(*this == *other) int32_t *p)
{
    if (p != NULL) {
        *p = 42;
    }
    if (other != NULL) {
        *other = 42;
    }
}
