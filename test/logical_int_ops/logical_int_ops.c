#include "pal.h"
#include <stdint.h>

int test_logical_and() {
    int x = 11;
    int y = 10;
    int z = x && y;
    return z;
}

int test_logical_or() {
    int x = 10;
    int y = 11;
    int z = x || y;
    return z;
}

int test_double_negation() {
    int x = 10;
    int y = 20;
    return !!x + !!y;
}

int test_negated_and() {
    int x = -10;
    int y = 10;
    int z = !(x && y);
    return z;
}
