#include "pal.h"
#include <stdint.h>

/*
 * A braced initializer for a scalar object. C permits it -- `int x = {0}` and
 * `T x = {}` -- and it is how a codebase writes an initializer that has to
 * compile against a typedef that is a struct on one platform and a plain
 * integer on another.
 *
 * The list holds at most one element, and it initializes the object directly.
 */

typedef uint32_t LE_UINT32;

typedef struct
{
    uint64_t Value;
} PAIR;

uint32_t
scalar_braced(void)
{
    LE_UINT32 zero = {0};
    LE_UINT32 seven = {7};
    uint32_t *p = {0};
    uint32_t empty = {};

    if (p != 0)
    {
        return 0;
    }

    return zero + seven + empty;
}

/*
 * The record case still goes through the record path, so a compound literal on
 * a struct is unaffected.
 */
uint64_t
record_braced(void)
{
    PAIR pair = {0};

    return pair.Value;
}
