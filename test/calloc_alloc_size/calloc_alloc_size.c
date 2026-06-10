#include "pal.h"
#include <stdlib.h>
#include <stdint.h>

void test_calloc_count_mul_size() {
    int *array = (int *) calloc(1, 3 * sizeof(int));
    _assert(array._length == 3);
    _assert(array[0] == 0);
    array[0] = 67;
    free(array);
}

void test_calloc_count_size_mul() {
    int *array = (int *) calloc(1, sizeof(int) * 4);
    _assert(array._length == 4);
    _assert(array[0] == 0);
    free(array);
}

void test_calloc_var_size(uint32_t n) {
    int *array = (int *) calloc(1, n * sizeof(int));
    free(array);
}
