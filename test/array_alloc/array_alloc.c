#include "pal.h"
#include <stdlib.h>
#include <stdint.h>

/* Allocating an array on the heap.
 *
 * `malloc(sizeof(T) * n)` hands back a block that is claimed at the array
 * view, so its elements carry their own initialisation state: reading one that
 * has not been written is a proof obligation the generated code fails, not
 * something the translator has to remember.
 *
 * `calloc` differs in exactly one way -- the storage arrives holding zeros --
 * and that is enough to make an element readable before it is written.
 *
 * Every case checks for null first. Allocation may fail, and until the source
 * has said what happens when it does there is no storage to own. */

/* 1 -- `malloc`: elements arrive uninitialised, so one has to be written
 * before it can be read. */
int32_t malloc_write_then_read(void) _ensures(return == 7) {
    int32_t *a = (int32_t *) malloc(sizeof(int32_t) * 4);
    if (a == NULL) {
        return 7;
    }
    a[2] = 7;
    int32_t v = a[2];
    free(a);
    return v;
}

/* 2 -- `calloc`: the zeros are part of what the allocator promised, so an
 * element reads as zero without being written. */
int32_t calloc_read_before_write(void) _ensures(return == 0) {
    int32_t *a = (int32_t *) calloc(3, sizeof(int32_t));
    if (a == NULL) {
        return 0;
    }
    int32_t v = a[1];
    free(a);
    return v;
}

/* 3 -- a written element still reads back as what was written. */
int32_t calloc_write_over_zero(void) _ensures(return == 9) {
    int32_t *a = (int32_t *) calloc(2, sizeof(int32_t));
    if (a == NULL) {
        return 9;
    }
    a[0] = 9;
    int32_t v = a[0];
    free(a);
    return v;
}

/* 4 -- the length is the count that was asked for. */
void length_is_the_count(void) {
    uint8_t *a = (uint8_t *) malloc(sizeof(uint8_t) * 16);
    if (a == NULL) {
        return;
    }
    _assert(a._length == 16);
    free(a);
}
