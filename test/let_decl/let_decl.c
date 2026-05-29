#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

_let(bool spec_id(bool x), x)

_let(_specint double_spec(_specint x), x + x)

_let(bool int_fits(_specint x), INT32_MIN <= x && x <= INT32_MAX)
_let(int double_int_spec(int x) requires(int_fits((_specint) x + x)), x + x)

void test_let(bool *p)
    _requires(*p == true)
    _ensures(*p == true)
{
    _assert(spec_id(*p) == true);
    _assert(double_spec(3) == 6);
    _assert(double_int_spec(3) == 6);
}
