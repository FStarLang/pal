#include "pal.h"

void test_fixed_array() {
    int arr[10];
    arr[0] = 42;
}

void test_vla(int len)
    _requires(len > 0 && len < 65536)
{
    int arr[len];
    arr[0] = 42;
}

/* Reading an element of a constant-sized stack-local array. */
int stack_array_read()
    _ensures(return == 42)
{
    int arr[2];
    arr[0] = 42;
    return arr[0];
}
    _ensures(return == 42)
{
    int arr[2];
    arr[0] = 42;
    return arr[0];
}
