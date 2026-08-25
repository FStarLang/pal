#include "pal.h"

#include <stdbool.h>
#include <stdint.h>

// C11 6.5.2.5p4 makes a compound literal an lvalue, so a named-constant macro
// that expands to one can appear anywhere a struct value can -- including as
// the base of a member access, which is how these two are almost always read.
typedef struct _SEQUENCE_VALUE
{
    uint64_t Value;
} SEQUENCE_VALUE;

#define SEQUENCE_VALUE_INVALID ((SEQUENCE_VALUE){.Value = 0})
#define SEQUENCE_VALUE_GET_RAW(v) ((v).Value)

bool
sequence_value_is_valid(SEQUENCE_VALUE Value)
    _ensures(return == (Value.Value != 0))
{
    return SEQUENCE_VALUE_GET_RAW(Value) != SEQUENCE_VALUE_GET_RAW(SEQUENCE_VALUE_INVALID);
}

uint64_t
compound_literal_field(void)
    _ensures(return == 7)
{
    return ((SEQUENCE_VALUE){.Value = 7}).Value;
}
