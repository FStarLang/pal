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

// A determined callee with a real body, whose contract is checked against it,
// asserted over both a literal and a variable argument.
_Bool
is_small(uint32_t x)
    _ensures(return == (_Bool)_inline_pulse(UInt32.v $(x) < 10))
{
    return x < 10u;
}

void
use_is_small(uint32_t x)
    _requires(x < 5u)
{
    _assert(is_small(3u));
    _assert(is_small(x));
}

// Inline Pulse can name the result directly, by the name the emitted contract
// binds it to. `return == (return && b)` says only "true implies `b`", and as
// a `rewrites_to` it would be `rewrites_to ret_implies_b (ret_implies_b && b)`,
// which no caller can solve. So it stays an ordinary equality.
_Bool
implies_b(_Bool b)
    _ensures(return == (_Bool)_inline_pulse(ret_implies_b && $(b)))
{
    return 0;
}

void
use_implies_b(_Bool b)
{
    if (implies_b(b))
    {
        _assert(b);
    }
}
