#include "pal.h"

_ghost_arg(float *v)
_preserves(_inline_pulse(ptr_pts_to $(q) 1.0R $(v)))
_plain float *read_fp(float **q _plain) {
    return *q;
}

_ghost_arg(int *v)
_preserves(_inline_pulse(ptr_pts_to $(p) 1.0R $(v)))
_plain float *bad_manual_public_call(int **p _plain) {
    return read_fp((float **)p);
}
