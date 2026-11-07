// A call may stand in an `_assert` only when its contract determines the
// result and its whole precondition is trivial. Pulse reads such a call as the
// term its `rewrites_to` names without checking the callee's precondition, so
// with one -- a `_requires`, or the ownership a pointer parameter implies --
// the assertion could name a call the source could not make.

#include "pal.h"

#include <stdint.h>

_pure _Bool
agrees(uint32_t A, uint32_t B);

_Bool
agree(uint32_t A, uint32_t B)
    _requires(A < 100)
    _ensures(return == (_Bool)_inline_pulse(Func_agrees.func_agrees $(A) $(B)));

void
check(uint32_t A, uint32_t B)
    _requires((_Bool)_inline_pulse(Func_agrees.func_agrees $(A) $(B)))
{
    _assert(agree(A, B));
}

// No `_requires`, but the pointer parameter makes the precondition own `*p`.
uint32_t
get(const uint32_t *p)
    _ensures(return == *p);

void
check_ptr(const uint32_t *p)
    _requires(*p == 1)
{
    _assert(get(p) == 1);
}
