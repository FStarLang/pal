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
