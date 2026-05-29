// Test: NULL pointer expressions
//
// Tests NULL as an rvalue (assignment, argument), and NULL comparisons (==, !=).
// Uses _plain on pointer parameters to skip pts_to pre/postconditions,
// since nullable pointers cannot satisfy pts_to when null.

#include "pal.h"
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

int32_t check_null(_plain int32_t *r) {
    if (r == NULL) {
        return 0;
    } else {
        return 1;
    }
}

int32_t call_check_null_with_null() {
    return check_null(NULL);
}

int32_t test_local_null() {
    int32_t *p = NULL;
    return (p == NULL);
}

int32_t test_nonnull_address() {
    int32_t x = 10;
    return (&x != NULL);
}

bool test_null_after_assignment(int *y) {
    int a, b;
    a = b = 3;
    return !y;
}