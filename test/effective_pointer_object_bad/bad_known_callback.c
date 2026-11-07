#include "pal.h"

_plain float *read_fp(float **q) {
    return *q;
}

_plain float *bad_known_callback(int **p) {
    _plain float *(*fp)(float **) = read_fp;
    return fp((float **)p);
}
