#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

/*
 * `_ensures(return == E)` is emitted as `rewrites_to ret E`. Each function
 * below has a body that really does return `E`, in one of the shapes the
 * translation accepts: arithmetic on a parameter, a `_Bool` result, a value
 * read through a non-const pointer, and `_old` of a pointee the function
 * changes. The `_bad` functions after them carry the same contracts over
 * bodies that do not meet them, and expected-verification-failures.txt
 * requires each to be rejected for its `rewrites_to`: the clause is checked
 * against the body, not assumed.
 */

uint32_t inc(uint32_t x) _ensures(return == x + 1u)
{
    return x + 1u;
}

bool is_zero(uint32_t x) _ensures(return == (x == 0u))
{
    return x == 0u;
}

uint32_t peek(uint32_t *p) _ensures(return == *p)
{
    return *p;
}

uint32_t bump(uint32_t *p)
    _requires(*p < 100u)
    _ensures(*p == _old(*p) + 1u)
    _ensures(return == _old(*p))
{
    uint32_t v = *p;
    *p = v + 1u;
    return v;
}

/* The caller sees each result only through its `rewrites_to`. */
uint32_t use_all(uint32_t *p)
    _requires(*p == 5u)
    _ensures(return == 13u)
{
    uint32_t a = inc(*p);
    _assert(a == 6u);
    uint32_t z = 1u;
    if (is_zero(*p))
    {
        z = 0u;
    }
    _assert(z == 1u);
    uint32_t r = bump(p);
    _assert(r == 5u);
    uint32_t q = peek(p);
    /* `p` is not const, so `peek` may have changed `*p`: only `q == *p` is known. */
    _assert(q == *p);
    return a + r + z + 1u;
}

/* The same contracts, unmet. */

uint32_t inc_bad(uint32_t x) _ensures(return == x + 1u)
{
    return x;
}

bool is_zero_bad(uint32_t x) _ensures(return == (x == 0u))
{
    return x != 0u;
}

uint32_t peek_bad(uint32_t *p) _ensures(return == *p)
{
    *p = *p + 1u;
    return 0u;
}

uint32_t bump_bad(uint32_t *p)
    _requires(*p < 100u)
    _ensures(*p == _old(*p) + 1u)
    _ensures(return == _old(*p))
{
    *p = *p + 1u;
    return *p;
}
