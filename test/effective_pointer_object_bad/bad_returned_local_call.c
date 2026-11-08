#include "pal.h"

_plain float **pretend(void *p _plain)
    _ensures((void *)return == p)
{
    return p;
}

_plain float *read_fp(float **q) {
    return *q;
}

_plain float *bad_returned_local_call(int **p) {
    float **q = pretend(p);
    return read_fp(q);
}
