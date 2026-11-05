#include "pal.h"
#include <stdint.h>

int32_t selected(int32_t input)
{
    return input + 1;
}

int32_t secondary(void);

int32_t caller(void)
    _ensures(return == 49)
{
    return selected(41) + secondary();
}

_Bool excluded(_out uint32_t *result)
{
    return __builtin_mul_overflow(-1, 2u, result);
}
