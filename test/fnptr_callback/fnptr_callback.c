// A callback parameter, in Palow's vocabulary.
//
// A function pointer's *value* -- which specification the code at that address
// meets -- is not carried by its bytes, so no points-to can grant it. It is
// the pure fact `is_valid f div pre post`, and a caller hands it over with a
// `_refine` on the parameter. That is the only way a body can call through a
// pointer whose target it does not know.
//
// The pre/post are recovered from the wrapper's *type* by `pre_of`/`post_of`,
// so the contract never has to be written twice; the call leaves them to
// slprop matching, because the fact in context is the author's and naming it
// here would mean reading the author's words.

#include "pal.h"
#include <stdint.h>

int32_t add(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return a + b;
}

int32_t apply(int32_t (*op)(int32_t, int32_t)
                  _refine((_slprop) _inline_pulse(
                      is_valid $(this) true
                          (pre_of Func_add.func_add__fp)
                          (post_of Func_add.func_add__fp))),
              int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return op(a, b);
}

// The same, with one argument, so the flat domain is not a tuple.
int32_t neg(int32_t a)
    _requires(a > -100 && a < 100)
    _ensures(return == -a)
{
    return -a;
}

int32_t apply1(int32_t (*op)(int32_t)
                   _refine((_slprop) _inline_pulse(
                       is_valid $(this) true
                           (pre_of Func_neg.func_neg__fp)
                           (post_of Func_neg.func_neg__fp))),
               int32_t a)
    _requires(a > -100 && a < 100)
    _ensures(return == -a)
{
    return op(a);
}

// Passing a concrete function to the callback. Decaying `add` to an address
// also establishes what the code there does, so no ghost step is needed at
// the call.
int32_t use_apply_add(void)
    _ensures(return == 5)
{
    return apply(add, 2, 3);
}

int32_t use_apply1_neg(void)
    _ensures(return == -7)
{
    return apply1(neg, 7);
}
