#include "pal.h"
#include <stdbool.h>

typedef struct {
    float f;
    double d;
} float_pair;

float id_float(float x) {
    return x;
}

double combine_float_double(float x, double y) {
    double z = (double) x;
    z = z + y;
    z = z - (double) 1;
    z = z * y;
    z = z / (double) 2;
    return z;
}

bool compare_double(double x, double y) {
    return x < y || x <= y || x == y;
}

void test_float_double(void) {
    float f = 1.25f;
    double d = 2.5;
    float_pair p = {.f = f, .d = d};

    f = -f;
    f = f + (float) 3;
    d = combine_float_double(f, p.d);

    p.f = (float) d;
    p.d = (double) id_float(p.f);

    bool b = (bool) d;
    b = b || compare_double(p.d, d);
    p.f = (float) b;
}
