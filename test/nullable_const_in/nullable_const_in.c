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

/*
 * A pointee whose field has a struct-level `_refine` is not handed a guard by
 * PAL: the refinement is a second guarded conjunct in the callee's contract,
 * and a guard PAL introduced at the zero value would compete with the
 * author's, which may name any value. The author introduces both.
 */
typedef struct _refine(this.lo <= this.hi) Range
{
    uint32_t lo;
    uint32_t hi;
} Range;

typedef struct Span
{
    uint32_t base;
    Range range;
} Span;

uint32_t read_optional_span(_nullable const Span* s)
{
    return 0;
}

uint32_t call_declined_span(void)
{
    uint32_t result;

    _ghost_stmt(
        intro_unless_null_null null (struct_Span_pts_to null 1.0R
            ({ fld_base = 7ul; fld_range = ({ fld_lo = 1ul; fld_hi = 2ul }) }));
        intro_unless_null_null null (pure (UInt32.v 1ul <= UInt32.v 2ul)));
    result = read_optional_span(NULL);
    _ghost_stmt(elim_unless_null_null null _; elim_unless_null_null null _);
    return result;
}

/*
 * Supplying a local is the author's too: the `_pts_to` guard needs the
 * pointer to be non-null, and both guards are taken apart after the call.
 */
uint32_t call_supplied_span(void)
{
    Span s;
    uint32_t result;

    s.base = 7;
    s.range.lo = 1;
    s.range.hi = 2;
    _ghost_stmt(struct_Span_pts_to_not_null loc_s);
    result = read_optional_span(&s);
    _ghost_stmt(
        elim_unless_null loc_s (struct_Span_pts_to loc_s 1.0R _);
        elim_unless_null loc_s (pure _));
    return result;
}

/*
 * A `_plain` nested struct does not carry its declaration's `_refine` into
 * the contract, so the guard is the `_pts_to` alone and PAL handles it.
 */
typedef struct PlainSpan
{
    uint32_t base;
    _plain Range range;
} PlainSpan;

uint32_t read_optional_plain_span(_nullable const PlainSpan* s)
{
    return 0;
}

uint32_t call_supplied_plain_span(void)
{
    PlainSpan s;

    s.base = 7;
    s.range.lo = 1;
    s.range.hi = 2;
    return read_optional_plain_span(&s);
}
