#include "pal.h"

_plain float *read_fp(float **q) {
    return *q;
}

_plain float *bad_call(int **p) {
    return read_fp((float **)p);
}
