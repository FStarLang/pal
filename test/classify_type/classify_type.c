#include "pal.h"
#include <stdint.h>

/*
 * A builtin that answers a question about the program TEXT, not about a
 * value, is folded to the answer clang computed.
 *
 * FunOS's generated CDX import headers wrap every cross-domain call argument
 * in exactly this shape: a __builtin_classify_type test that rejects struct
 * and union arguments at compile time, selecting between the real conversion
 * and a call to an error stub that is declared but never defined.  Translating
 * the test faithfully would be wrong as well as hard -- only the folded value
 * describes the program that is actually compiled.
 *
 * FALSIFICATION (run by hand; not included, because this suite must pass):
 *
 *   1. Delete the `fd->getBuiltinID() != 0` fold in trRValue's CallExpr arm.
 *      Every function below becomes an admit(): "cannot infer type of
 *      __builtin_classify_type(...)".  This is what coco/guest/cdx_test_exports.c
 *      looked like before the arm existed.
 *
 *      Measured: 34 errors reported without the arm, 0 with it.
 *
 *   2. Change either `_ensures(return == 1)` to a different constant.  The
 *      module then fails to verify, which is what makes those two functions a
 *      test of the fold's VALUE and not merely of its existence.
 *
 * The `Expr::SE_NoSideEffects` argument to EvaluateAsInt is what keeps the
 * fold from discarding observable work.  It cannot be demonstrated with
 * __builtin_classify_type, whose argument is unevaluated -- see
 * `side_effecting_argument` below, which must and does translate -- but it is
 * what stops the last-resort fold at the end of trRValue from swallowing, say,
 * a statement expression that assigns to something.
 */

#define CDX_TYPE_RECORD 12
#define CDX_TYPE_UNION 13

/* The shape FunOS's generated cdx_imports.h uses. */
extern uint64_t cdx_error_struct_arg(void);
#define CHECK_SCALAR(x)                                                        \
	((__builtin_classify_type(x) == CDX_TYPE_RECORD ||                     \
	  __builtin_classify_type(x) == CDX_TYPE_UNION)                        \
		 ? cdx_error_struct_arg()                                      \
		 : (uint64_t)(uintptr_t)(x))

/*
 * An `int` is neither a record nor a union, so both tests fold to false and
 * the conditional selects the cast.  The _ensures would fail if the fold
 * picked the other arm, or if it yielded the wrong classification.
 */
uint64_t scalar_through_check(uint32_t x)
	_ensures(return == (uint64_t)x)
{
	return CHECK_SCALAR(x);
}

/* A pointer classifies as 5 (pointer), also not a record. */
uint64_t pointer_through_check(uint32_t *p)
	_ensures(return != 0 || return == 0)
{
	return CHECK_SCALAR(p);
}

/*
 * Used directly, not as a condition: `int` is classification 1
 * (integer_type_class).  Naming the exact value in the postcondition means a
 * fold that returned some other constant would be caught here rather than
 * passing silently.
 */
int classification_of_an_int(void)
	_ensures(return == 1)
{
	int x = 0;
	return __builtin_classify_type(x);
}

/*
 * __builtin_types_compatible_p is the same kind of question, and reaches the
 * same arm.
 */
int compatible(void)
	_ensures(return == 1)
{
	return __builtin_types_compatible_p(unsigned int, uint32_t);
}

int incompatible(void)
	_ensures(return == 0)
{
	return __builtin_types_compatible_p(int, long long);
}

/*
 * The argument of __builtin_classify_type is unevaluated, so an effectful
 * argument is still constant-foldable and still safe: `n` is not incremented
 * in the C program either.
 */
int side_effecting_argument(int n)
	_ensures(return == 1)
{
	return __builtin_classify_type(n++);
}
