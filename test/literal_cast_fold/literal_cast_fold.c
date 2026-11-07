#include "pal.h"
#include <stdint.h>

/* Masks assembled from casts of representable literals. normalize_casts used
 * to keep such casts as Int.Cast applications, leaving the solver one
 * signed-modulo refinement per constant; both postconditions failed to verify
 * (Error 19). Folding the casts to constants of the target type makes them
 * plain arithmetic facts. */
uint32_t nibble_mask(void)
    _ensures(return == 0xF0F0F0F0u)
{
    return ((uint32_t)0xF0 << 24) | ((uint32_t)0xF0 << 16) |
           ((uint32_t)0xF0 << 8) | (uint32_t)0xF0;
}

uint64_t wide_mask(void)
    _ensures(return == 0x00FF00FF00FF00FFull)
{
    return ((uint64_t)0xFF << 48) | ((uint64_t)0xFF << 32) |
           ((uint64_t)0xFF << 16) | (uint64_t)0xFF;
}
