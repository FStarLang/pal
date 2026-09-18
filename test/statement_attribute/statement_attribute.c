#include "pal.h"
#include <stdint.h>

int32_t explicit_fallthrough(int32_t x)
    _ensures(x == 0 ==> return == 11)
    _ensures(x == 1 ==> return == 1)
    _ensures((x != 0 && x != 1) ==> return == 20)
{
    int32_t result = 0;
    switch (x) {
    case 0:
        result = 10;
        __attribute__((fallthrough));
    case 1:
        result = result + 1;
        break;
    default:
        result = 20;
        break;
    }
    return result;
}

static void set_value(int32_t *p)
    _ensures(*p == 42)
{
    *p = 42;
}

int32_t attributed_call(void)
    _ensures(return == 42)
{
    int32_t value = 0;
    /* GCC does not support nomerge on statements. */
#ifdef __clang__
    __attribute__((nomerge))
#endif
    set_value(&value);
    return value;
}
