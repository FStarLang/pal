#include "pal.h"
#include <stdint.h>

// Test cast acceptance without assuming a particular integer representation.

long typed_pointer_to_long(_plain int32_t *p)
{
    return (long)p;
}

unsigned long typed_pointer_to_unsigned_long(_plain int32_t *p)
{
    return (unsigned long)p;
}

long void_pointer_to_long(void *p)
{
    return (long)p;
}

unsigned long void_pointer_to_unsigned_long(void *p)
{
    return (unsigned long)p;
}
