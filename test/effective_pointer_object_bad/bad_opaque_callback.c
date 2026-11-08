#include "pal.h"

typedef _plain float *float_address;

float_address read_fp(float **q) {
    return *q;
}

void anchor(void) {
    float_address (*fp)(float **) = read_fp;
}

float_address bad_opaque_callback(
    float_address (*fp)(float **)
        _refine((_slprop) _inline_pulse(
            Pulse.Lib.C.Palow.FnPtr.is_valid $(this) true
              (Pulse.Lib.C.Palow.FnPtr.pre_of Funcptr_read_fp.func_read_fp__fp)
              (Pulse.Lib.C.Palow.FnPtr.post_of Funcptr_read_fp.func_read_fp__fp))),
    int **p) {
    return fp((float **)p);
}
