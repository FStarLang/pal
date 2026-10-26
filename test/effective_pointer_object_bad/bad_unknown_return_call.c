#include "pal.h"

_plain float **unknown_source(void *p _plain)
    _ensures((void *)return == p)
{
    if (p)
        return p;
    return p;
}

_plain float *read_fp(float **q) {
    return *q;
}

_plain float *bad_unknown_return_call(int **p) {
    return read_fp(unknown_source(p));
}
