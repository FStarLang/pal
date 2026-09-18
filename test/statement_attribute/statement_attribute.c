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
