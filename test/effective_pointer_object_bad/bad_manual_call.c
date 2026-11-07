#include "pal.h"

_ghost_arg(float *v)
_preserves(_inline_pulse(ptr_pts_to $(q) 1.0R $(v)))
_plain float *read_fp(float **q _plain) {
    return *q;
}

_plain float *bad_manual_call(int **p) {
    return read_fp((float **)p);
}
