#include "pal.h"
#include <stddef.h>
#include <stdint.h>

typedef struct Point
{
    uint32_t x;
    uint32_t y;
} Point;

typedef const Point* PCPoint;

/*
 * An optional *const* input. The callee owns nothing until it has tested the
 * pointer, and under the test its permission and pointee value are implicits
 * of the signature, so a caller gets back the very hold it passed in.
 *
 * The interesting call site is the one that declines the input: it holds
 * nothing to solve those implicits against. PAL introduces the (empty) guard
 * there explicitly, at full permission and the pointee type's canonical zero,
 * which pins both. The resource is `emp` because the pointer is null, so the
 * choice says nothing about memory.
 */
uint32_t read_optional(_nullable PCPoint p)
{
    uint32_t result;

    if (p != NULL)
    {
        result = p->x;
    }
    else
    {
        result = 0;
    }

    return result;
}

/* Declines the optional input. */
uint32_t call_declined(void)
{
    uint32_t result;

    result = read_optional(NULL);
    return result;
}

/* Forwards its own optional input, held at whatever fraction its caller had. */
uint32_t call_forwarded(_nullable PCPoint p)
{
    uint32_t result;

    result = read_optional(p);
    return result;
}

typedef struct Pair
{
    Point a;
    Point b;
} Pair;

typedef const Pair* PCPair;

/*
 * Passes the address of a member of a structure it only borrows. This is what
 * the `_mutable` workaround used to make impossible: a parameter demanding
 * full permission cannot be satisfied from a fractional hold.
 */
uint32_t call_borrowed_member(PCPair q)
{
    uint32_t result;

    // NOTE: written through a local rather than as `return read_optional(...)`
    // because PAL emits a call's closing ghost steps after the `return`, where
    // they are unreachable. See the ghost-after-return note in the PAL tests.
    result = read_optional(&q->a);
    return result;
}
