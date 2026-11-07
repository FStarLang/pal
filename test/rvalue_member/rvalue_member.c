#include "pal.h"

#include <stdint.h>

struct pair {
    uint32_t lo;
    uint32_t hi;
};

static struct pair make_pair(uint32_t lo, uint32_t hi)
    _ensures(return.lo == lo)
    _ensures(return.hi == hi)
{
    struct pair p = { 0 };
    p.lo = lo;
    p.hi = hi;
    return p;
}

/* Member access on the result of a call: the base is an rvalue structure,
   so there is no lvalue to project from. */
uint32_t low_of(uint32_t lo, uint32_t hi)
    _ensures(return == lo)
{
    return make_pair(lo, hi).lo;
}

/* Nested projection through a value-typed field. */
struct nested {
    struct pair inner;
};

static struct nested make_nested(uint32_t lo, uint32_t hi)
    _ensures(return.inner.lo == lo)
    _ensures(return.inner.hi == hi)
{
    struct nested n = { 0 };
    n.inner = make_pair(lo, hi);
    return n;
}

uint32_t high_of_nested(uint32_t lo, uint32_t hi)
    _ensures(return == hi)
{
    return make_nested(lo, hi).inner.hi;
}

/* The increment must only be evaluated in the selected arm. */
uint32_t conditional_low_of(uint32_t lo, uint32_t hi, int take)
    _requires(!take || lo < UINT32_MAX)
    _ensures(return == (take ? lo + 1 : hi))
{
    if (take)
        return make_pair(lo + 1, hi).lo;
    return hi;
}

/* Member reads of a call result in statement position: assignment,
   compound assignment and call argument. */
uint32_t assign_low_of(uint32_t lo, uint32_t hi)
    _ensures(return == lo)
{
    uint32_t x = 0;
    x = make_pair(lo, hi).lo;
    return x;
}

uint32_t add_high_of(uint32_t lo, uint32_t hi)
    _requires(hi < UINT32_MAX)
    _ensures(return == hi + 1)
{
    uint32_t x = 1;
    x += make_pair(lo, hi).hi;
    return x;
}

static void expect_equal(uint32_t actual, uint32_t expected)
    _requires(actual == expected)
{
}

void pass_low_of(uint32_t lo, uint32_t hi)
{
    expect_equal(make_pair(lo, hi).lo, lo);
}
