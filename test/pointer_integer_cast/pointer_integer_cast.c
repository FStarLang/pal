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

typedef long signed_address;
typedef unsigned long unsigned_address;

signed_address pointer_to_signed_alias(void *p)
{
    return (signed_address)p;
}

unsigned_address pointer_to_unsigned_alias(void *p)
{
    return (unsigned_address)p;
}

long local_address_to_long(void)
{
    int32_t x = 42;
    long address = (long)&x;
    return address;
}

unsigned long local_address_to_unsigned_long(void)
{
    int32_t x = 42;
    unsigned long address = (unsigned long)&x;
    return address;
}

unsigned long array_to_unsigned_long(_array int32_t *p)
{
    return (unsigned long)p;
}

long arrayptr_to_long(_arrayptr int32_t *p)
{
    return (long)p;
}

static void *record_call(void *p, int32_t *count)
    _requires(*count == 0)
    _ensures(*count == 1)
    _ensures(return == p)
{
    *count = 1;
    return p;
}

long call_to_long(void *p)
{
    int32_t count = 0;
    long result = (long)record_call(p, &count);
    _assert(count == 1);
    return result;
}

unsigned long call_to_unsigned_long(void *p)
{
    int32_t count = 0;
    unsigned long result = (unsigned long)record_call(p, &count);
    _assert(count == 1);
    return result;
}
