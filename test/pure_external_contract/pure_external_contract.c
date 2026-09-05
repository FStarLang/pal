// A `_pure` function without a body is an external pure operation. It is
// assumed as a pure F* value, so it can be named in the contracts of the
// functions that call it. A checked-arithmetic routine is the motivating case:
// its result is only meaningful when its status says it did not overflow, and
// that status is classified by another external pure operation.

#include "pal.h"

#include <stdint.h>

_pure _Bool
failed(int Status);

// Declared once without a contract, as an external header would provide it,
// and again with the contract that header documents. Clang merges the two, so
// the contract applies without the first declaration having to change.
int
checked_add(uint32_t A, uint32_t B, _out uint32_t* Result);

// `*Result >= A` is unsigned wraparound saying the true sum fits: adding B
// wraps exactly when the mathematical sum leaves the 32-bit range.
int
checked_add(uint32_t A, uint32_t B, _out uint32_t* Result)
    _ensures(failed(return) || (*Result == A + B && *Result >= A));

// Provable only from the contract above: on the path the status accepts, the
// result is the exact mathematical sum rather than a wrapped one.
uint32_t
saturating_add(uint32_t X, uint32_t Y)
    _ensures(_inline_pulse(
        pure (FStar.UInt32.v $(return) <= FStar.UInt32.v $(X) + FStar.UInt32.v $(Y))))
{
    uint32_t sum = 0;
    int status;

    status = checked_add(X, Y, &sum);
    if (failed(status))
    {
        sum = 0;
    }

    return sum;
}
