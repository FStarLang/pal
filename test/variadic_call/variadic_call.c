#include "pal.h"
#include <stdint.h>

int32_t read_first_pointer(int32_t *first, ...)
    _ensures(return == *first)
{
    return *first;
}

int32_t call_with_extra_pointers(void)
    _ensures(return == 42)
{
    int32_t first = 42;
    int32_t second = 7;
    int32_t third = 9;
    return read_first_pointer(&first, &second, &third);
}
