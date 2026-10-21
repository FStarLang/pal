#include "pal.h"
#include <stdint.h>
#define UNIT_VALUE 2
#include "private.h"

static const int32_t private_number = 2;
extern const int external_array[];
extern const int external_number;
static int32_t private_value(void) _ensures(return == 2) { return 2; }

int32_t external_value(int32_t other) _ensures(return == other);
int32_t array_b(void) _ensures(return == 4) { return external_array[1]; }
int32_t external_object(void) _ensures(return == 5) { return external_number; }
int32_t genuine_b(void) _ensures(return == 2) { return private_value(); }
int32_t object_b(void) _ensures(return == 2) { return private_number; }
int32_t header_b(void) _ensures(return == 2) { return header_value(); }
_plain int32_t *address_b(void) { return header_address(); }
int32_t write_b(void)
    _requires(_live(header_cell)) _ensures(_live(header_cell))
    _ensures(return == 2)
{
    header_cell = 2;
    return header_cell;
}
int32_t call_external(void) _ensures(return == 3) { return external_value(3); }
int32_t false_function_b(void) _ensures(return == 1) { return private_value(); }
int32_t false_object_b(void) _ensures(return == 1) { return private_number; }
