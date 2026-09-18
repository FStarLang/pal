/*
 * The comma operator in rvalue position.
 *
 * `(a, b)` evaluates `a`, discards it, then yields `b`.  PAL's expression IR
 * has nowhere to put `a` -- there is no statement sequencing inside an
 * rvalue -- so it translates the form only when `a` cannot be observed, i.e.
 * when Clang reports that it has no side effects.  Then `(a, b)` and `b` are
 * the same program and the arm is a pure simplification.
 *
 * The case this exists for is FunOS's generated CDX import macros, which are
 * all of the shape
 *
 *     #define f(...) ((void)sizeof(f(__VA_ARGS__)), (uint64_t)invoke_N(...))
 *
 * -- a compile-time prototype check, whose operand is unevaluated, followed by
 * the real call.  Refusing it made every cross-domain call site an `admit()`,
 * which discards the surrounding obligations along with it.
 *
 * FALSIFICATION.  Deliberately NOT in this file, because this suite has to
 * pass.  A left operand that DOES have a side effect must still be refused,
 * or the arm would be silently changing the program.  Checked by appending
 *
 *     uint64_t FALSIFY_effectful(uint64_t a)
 *     {
 *             int i = 0;
 *             return (i++, (uint64_t)i) + a;
 *     }
 *
 * which gives, as required:
 *
 *     error: unsupported rvalue expression BinaryOperator
 *        |     return (i++, (uint64_t)i) + a;
 *        |             ^^^^^^^^^^^^^^^^
 */

#include "pal.h"
#include <stdint.h>

uint64_t callee(uint64_t a, uint64_t b)
    _ensures(return == a + b)
{
    return a + b;
}

/* The shape a generated CDX import expands to. */
#define cdx_callee(...) \
    ((void)sizeof(callee(__VA_ARGS__)), (uint64_t)callee(__VA_ARGS__))

uint64_t through_cdx_macro(uint64_t a, uint64_t b)
    _ensures(return == a + b)
{
    return cdx_callee(a, b);
}

/* A discarded operand that is a plain constant. */
uint64_t comma_constant(uint64_t a)
    _ensures(return == a)
{
    return (0, a);
}

/*
 * The discarded operand is really discarded: this returns `a`, not `b`.  The
 * postcondition is what pins that down -- were the arm to yield the LEFT
 * operand, this would fail rather than silently pass.
 */
uint64_t comma_reads_param(uint64_t a, uint64_t b)
    _ensures(return == a)
{
    return (b, a);
}

/* Nested, and in argument position rather than return position. */
uint64_t comma_nested(uint64_t a, uint64_t b)
    _ensures(return == a + b)
{
    return callee((0, a), (1, (2, b)));
}
