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

/* Arguments that read no memory beyond locals and cannot be undefined: string
   literals, constant expressions, a decayed local array, integer conversions,
   and wrapping (unsigned) arithmetic with in-range constant shifts. */
int32_t call_with_inert_computations(uint32_t word, uint64_t hi, uint64_t lo)
    _ensures(return == 42)
{
    int32_t first = 42;
    char name[4] = {0};
    return read_first_pointer(&first, "literal", sizeof(first) * 2, (1u << 3),
                              name, (char)((word >> 24) & 0xff), hi - lo,
                              ~word, word ^ 5u);
}
