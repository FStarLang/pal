#pragma once
#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

static inline int32_t shared_increment(int32_t x)
    _requires(x >= 0 && x < 100)
    _ensures(return == x + 1)
{
    return x + 1;
}

static inline _total int32_t shared_zero(void) _ensures(return == 0) {
    return 0;
}

static inline _pure bool shared_not(bool x) _ensures(return == !x) {
    return !x;
}

static inline int32_t shared_read(int32_t *p) _ensures(return == *p) {
    return *p;
}

static inline int32_t shared_ghost(_plain int32_t *p)
    _ghost_arg(int32_t v)
    _preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(p) #1.0R $(v)))
    _ensures(return == v)
{
    return *p;
}

static inline int32_t variant_body(void) _ensures(return == UNIT_VALUE) {
    return UNIT_VALUE;
}

static inline int32_t variant_contract(int32_t x)
    _requires(x == UNIT_VALUE) _ensures(return == x)
{
    return x;
}

static const int32_t private_number = 3;
static inline int32_t private_read(void) _ensures(return == 3) {
    return private_number;
}

static inline int32_t addressed(void) _ensures(return == 7) {
    return 7;
}
