#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

/* A function name passed as an argument is a function pointer whose validity
   the caller establishes for the call and drops after it.

   Regression guard: a call used as a statement, of a function returning void,
   kept that validity until the end of the function. Inside one arm of a
   conditional, the arm then discarded what it had established, and the
   function was left with a validity resource it could not account for. */

typedef void (*visit_fn)(int32_t value);

void visit(int32_t value);

void apply(visit_fn f, int32_t value);

void apply_when(bool b, int32_t value)
{
    if (b)
    {
        apply(visit, value);
    }
    else
    {
        apply(visit, value + 0);
    }
}

void apply_one_arm(bool b, int32_t value)
{
    if (b)
    {
        apply(visit, value);
    }
}

int32_t apply_then(bool b, int32_t value)
{
    int32_t r = 0;
    if (b)
    {
        apply(visit, value);
        r = 1;
    }
    r = r + 1;
    return r;
}

int32_t apply_or_stop(bool b, int32_t value)
    _requires(b)
{
    int32_t r = 0;
    if (b)
    {
        apply(visit, value);
    }
    else
    {
        _assert(false);
    }
    r = 1;
    return r;
}
