#include "pal.h"
#include <stdbool.h>

#define MAX_ERROR 4095L

void *integer_to_pointer(long x)
{
    return (void *)x;
}

long pointer_to_integer(void *p)
{
    return (long)p;
}

unsigned long pointer_to_unsigned(void *p)
{
    return (unsigned long)p;
}

bool is_error_pointer(void *p)
{
    unsigned long address = pointer_to_unsigned(p);
    return address >= (unsigned long)(-MAX_ERROR);
}

long error_or_zero(void *p)
{
    if (is_error_pointer(p))
        return pointer_to_integer(p);

    return 0;
}

/* Target 1: every error in the reserved range is recognized and recovered. */
long test_error_roundtrip(long error)
    _requires(error >= -MAX_ERROR && error < 0)
    _ensures(return == error)
{
    void *p = integer_to_pointer(error);

    bool is_error = is_error_pointer(p);
    _assert(is_error);

    long decoded = pointer_to_integer(p);
    _assert(decoded == error);

    return error_or_zero(p);
}

/* Target 2: integer zero produces NULL, which is not an error. */
void test_null(void)
{
    void *p = integer_to_pointer(0);
    _assert(p == (void *)0);

    unsigned long address = pointer_to_unsigned(p);
    _assert(address == 0);

    bool is_error = is_error_pointer(p);
    _assert(!is_error);

    long result = error_or_zero(p);
    _assert(result == 0);
}

/* Target 3: the error-range boundary is exact. */
void test_error_boundary(void)
{
    void *inside = integer_to_pointer(-MAX_ERROR);
    void *outside = integer_to_pointer(-MAX_ERROR - 1L);

    bool inside_is_error = is_error_pointer(inside);
    bool outside_is_error = is_error_pointer(outside);

    _assert(inside_is_error);
    _assert(!outside_is_error);

    long result = error_or_zero(outside);
    _assert(result == 0);
}
