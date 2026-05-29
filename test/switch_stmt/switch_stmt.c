#include "pal.h"
#include <stdint.h>

/* Simple switch with break in every case */
int32_t day_type(int32_t day)
    _requires(day >= 0 && day <= 6)
    _ensures(day >= 1 && day <= 5 ==> return == 1)
    _ensures(day == 0 || day == 6 ==> return == 0)
{
    int32_t result = 0;
    switch (day) {
    case 1:
    case 2:
    case 3:
    case 4:
    case 5:
        result = 1;
        break;
    default:
        result = 0;
        break;
    }
    return result;
}

/* Switch with fall-through */
int32_t classify(int32_t x)
    _requires(x >= 0 && x <= 3)
{
    int32_t r = 0;
    switch (x) {
    case 0:
        r = 10;
        break;
    case 1:
    case 2:
        r = 20;
        break;
    default:
        r = 30;
        break;
    }
    return r;
}
