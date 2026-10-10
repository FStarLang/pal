#include "pal.h"
#include <stdlib.h>
#include <stdint.h>

void test_calloc_count_mul_size() {
    int *array = (int *) calloc(1, 3 * sizeof(int));
    if (array == NULL) {
        return;
    }
    _assert(array._length == 3);
    _assert(array[0] == 0);
    array[0] = 67;
    free(array);
}

void test_calloc_count_size_mul() {
    int *array = (int *) calloc(1, sizeof(int) * 4);
    if (array == NULL) {
        return;
    }
    _assert(array._length == 4);
    _assert(array[0] == 0);
    free(array);
}

/* A count that is not written down leaves a real size obligation: `n *
   sizeof(int)` is computed in `size_t` and C gives it no meaning when it
   overflows. Nothing but the function's own `_requires` can discharge it. */
void test_calloc_var_size(uint32_t n) _requires(n <= 1000) {
    int *array = (int *) calloc(1, n * sizeof(int));
    if (array == NULL) {
        return;
    }
    free(array);
}
