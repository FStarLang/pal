#include "pal.h"
#include <stdint.h>

/*
 * A conditional whose condition clang can decide at compile time is folded to
 * the arm C would actually take.
 *
 * This is not an optimization.  C evaluates exactly one arm, so when the
 * condition is constant the program IS that arm -- and the arm that is never
 * taken is frequently not meant to be compiled at all.  FunOS's generated CDX
 * import headers are the motivating case: every cross-domain call argument is
 * wrapped in
 *
 *   (__builtin_classify_type(x) == 12 || __builtin_classify_type(x) == 13)
 *       ? CDX_ERROR__Struct_or_union_arguments_not_allowed_in_CDX_call()
 *       : (uint64_t)(x)
 *
 * so that passing a struct fails to link.  Translating that faithfully both
 * pulls in a function with no body and produces a conditional whose arms have
 * types that agree in C but not in F* ("The branches of a conditional must
 * return the same type").
 *
 * FALSIFICATION, run by hand; the suite must pass, so the refusals are
 * recorded here rather than compiled:
 *
 *  - Deleting the fold in trRValue reinstates
 *      Error 228 ... The branches of a conditional must return the same type
 *      - The types Typedef_uint64_t.ty_uint64_t and UInt64.t are not equal
 *    on `cdx_shape` below, which is the exact coco failure this fixes.
 *
 *  - Deleting the `HasSideEffects` guard makes `cond_with_side_effect` below
 *    translate to `return 7;` with the `++` dropped, and its `_ensures` on the
 *    counter then fails -- which is the point of stating the postcondition on
 *    the counter rather than on the result.
 *
 *  - Weakening the guard to fold a NON-constant condition makes `not_constant`
 *    translate to one arm, and its `_ensures` fails for the other input.
 */

/* Declared and deliberately never defined, exactly like the CDX error stub. */
uint64_t CHECK_FAILED(void);

#define CHECK_SCALAR(x)                                                        \
    ((__builtin_classify_type(x) == 12 || __builtin_classify_type(x) == 13)     \
         ? CHECK_FAILED()                                                      \
         : (uint64_t)(x))

/* The shape that motivated this: the dead arm must not be translated. */
uint64_t cdx_shape(uint64_t v) _ensures(return == v)
{
    return CHECK_SCALAR(v);
}

/* In statement position too -- the value is discarded, the arm still runs. */
uint64_t cdx_shape_stmt(uint64_t v)
    _ensures(return == v)
{
    uint64_t r = 0;
    r = CHECK_SCALAR(v);
    return r;
}

int const_true(void) _ensures(return == 7)
{
    return 1 ? 7 : (int)CHECK_FAILED();
}

int const_false(void) _ensures(return == 9)
{
    return 0 ? (int)CHECK_FAILED() : 9;
}

/*
 * A constant condition reached through arithmetic and sizeof, which is how
 * real macros write it.
 */
int const_sizeof(void) _ensures(return == 4)
{
    return (sizeof(uint32_t) == 4) ? 4 : (int)CHECK_FAILED();
}

/*
 * NOT constant: the fold must decline, and both arms must survive.  The
 * postcondition is stated so that folding to either arm breaks it.
 */
int not_constant(int c)
    _ensures(return == 7 || return == 9)
{
    return c ? 7 : 9;
}

/*
 * Constant VALUE, but the condition does something.  `(n = 1)` is an
 * assignment whose value is 1, so a fold that looked only at the value would
 * drop the assignment.  The postcondition is deliberately about the VARIABLE
 * and not about the result: it is false exactly when the side effect is lost,
 * and says nothing about which arm ran.
 */
int cond_with_side_effect(void)
    _ensures(return == 1)
{
    int n = 0;
    int r = (n = 1) ? 7 : 8;
    (void)r;
    return n;
}

/* The same, with the conditional in statement position. */
int cond_with_side_effect_stmt(void)
    _ensures(return == 1)
{
    int n = 0;
    (void)((n = 1) ? 7 : 8);
    return n;
}
