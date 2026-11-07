#include "pal.h"
#include <stdint.h>

#define UNIT_VALUE 1
#include "private.h"

static const int32_t private_number = 1;
const int32_t external_array[2] = {3, 4};
const int32_t external_number = 5;
static int32_t private_value(void) _ensures(return == 1) { return 1; }

int32_t external_value(int32_t value) _ensures(return == value) { return value; }
int32_t array_a(void) _ensures(return == 3) { return external_array[0]; }
int32_t genuine_a(void) _ensures(return == 1) { return private_value(); }
int32_t object_a(void) _ensures(return == 1) { return private_number; }
int32_t header_a(void) _ensures(return == 1) { return header_value(); }
_plain int32_t *address_a(void) { return header_address(); }
int32_t pointer_a(void) _ensures(return == 1) {
    int32_t (*fn)(void) = &private_value;
    int32_t (*bare)(void) = private_value;
    return private_value();
}
int32_t write_a(void)
    _requires(_live(header_cell)) _ensures(_live(header_cell))
    _ensures(return == 1)
{
    header_cell = 1;
    return header_cell;
}
int32_t annotated_a(void)
    _ensures(_inline_pulse(pure ($(return) == $(private_number))))
{
    return private_value();
}
int32_t parameter_shadow(int32_t private_number)
    _ensures(_inline_pulse(pure ($(return) == $(private_number))))
{
    return private_number;
}
int32_t block_shadow(void) _ensures(return == 1) {
    { int32_t private_number = 7; }
    return private_number;
}
int32_t false_function_a(void) _ensures(return == 2) { return private_value(); }
int32_t false_object_a(void) _ensures(return == 2) { return private_number; }
