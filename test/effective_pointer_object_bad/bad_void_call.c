#include "pal.h"

_plain float *read_fp(float **q) {
    return *q;
}

_plain float *bad_void_call(void *p _plain) {
    return read_fp((float **)p);
}
