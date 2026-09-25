#include "pal.h"
#include <stdint.h>

int32_t read_first_pointer(int32_t *first, ...)
    _ensures(return == *first)
    _preserves_value(*first)
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

int32_t call_without_extra_arguments(void)
    _ensures(return == 42)
{
    int32_t first = 42;
    return read_first_pointer(&first);
}

int32_t call_with_extra_values(int32_t value)
    _ensures(return == 42)
{
    int32_t first = 42;
    uint8_t small = 7;
    int32_t *pointer = &first;
    return read_first_pointer(&first, value, small, pointer, 9, 1.5, 'a');
}

int32_t read_second_pointer(int32_t *first, int32_t *second, ...)
    _ensures(return == *second)
    _preserves_value(*first)
    _preserves_value(*second)
{
    return *second;
}

int32_t call_with_two_fixed_arguments(void)
    _ensures(return == 7)
{
    int32_t first = 42;
    int32_t second = 7;
    int32_t extra = 9;
    return read_second_pointer(&first, &second, &extra);
}
