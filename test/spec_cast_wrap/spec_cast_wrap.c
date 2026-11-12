#include "pal.h"
#include <stdint.h>

#include <stddef.h>
#include <limits.h>

/* A contract's cast to an unsigned type is C's conversion: it reduces modulo
   the type's range, as the body's does. */
size_t ones(void)
    _ensures(return == (size_t)-1 / UCHAR_MAX)
    _ensures(return == 0x0101010101010101)
{
    return (size_t)-1 / UCHAR_MAX;
}

void constants(int y)
    _requires(-100 < y && y < 100)
{
    _assert((size_t)-1 > 0);
    _assert((uint8_t)300 == 44);
    _assert((int8_t)200 == -56);
    _assert(y >= 1 || (uint32_t)(y - 1) > 100);
    _assert(_forall(_specint k, (uint8_t)k < 256 && (int8_t)k >= -128));
    _assert(_forall(_specint k, 0 <= k && k < 10 ==> (size_t)k == k));
}

/* Both of these held when a contract read the cast as the number itself;
   neither is true in C, so both must fail
   (expected-verification-failures.txt). */
void minus_one_is_small(void)
{
    _assert((size_t)-1 < 1);
}

void low_byte_is_everything(int y)
    _requires(0 <= y && y < 1000)
{
    _assert((uint8_t)(y + 1) == y + 1);
}
