// A postcondition that fixes the result to a Pulse-level function of the
// arguments -- `_ensures(return == (_Bool)_inline_pulse(f $(A) $(B)))` -- is
// emitted as Pulse's `rewrites_to`, the same as when the right-hand side is a
// plain C expression.
//
// That is not cosmetic. Pulse's impure-spec elaborator, which is what turns an
// `_assert` over a stateful call into a proposition, looks for exactly a
// `rewrites_to` in the callee's postcondition; an ordinary equality leaves it
// with nothing to name the result by, and the assertion does not elaborate at
// all. So `screen` below is the regression: it only translates if `agree`'s
// contract determines its result.

#include "pal.h"

#include <stdint.h>

// An external pure operation, assumed as a pure F* value. It stands for the
// vocabulary predicate a real contract would name.
_pure _Bool
agrees(uint32_t A, uint32_t B);

// Decides `agrees`.
_Bool
agree(uint32_t A, uint32_t B)
    _ensures(return == (_Bool)_inline_pulse(Func_agrees.func_agrees $(A) $(B)));

// Requires it, in the shape of a routine that asserts its precondition fatally
// rather than returning a verdict.
uint32_t
combine(uint32_t A, uint32_t B)
    _requires((_Bool)_inline_pulse(Func_agrees.func_agrees $(A) $(B)));

// The impure-spec use: asserting a stateful call needs the call's result to be
// nameable as a pure term.
uint32_t
checked_combine(uint32_t A, uint32_t B)
    _requires((_Bool)_inline_pulse(Func_agrees.func_agrees $(A) $(B)))
{
    _assert(agree(A, B));
    return combine(A, B);
}

// And the caller that discharges the assertion by screening first.
uint32_t
screen(uint32_t A, uint32_t B)
{
    if (!agree(A, B))
    {
        return 0;
    }

    return checked_combine(A, B);
}
