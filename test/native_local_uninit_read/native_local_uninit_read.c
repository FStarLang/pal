#include "pal.h"
#include <stdint.h>

void *read_initialized(void **p)
{
    return *p;
}

void *read_forgotten(void *value)
{
    void *p = value;
    _ghost_stmt(Pulse.Lib.C.Palow.Scalar.ptr_forget $&(p));
    _assert((_slprop)_inline_pulse(Pulse.Lib.C.Palow.Scalar.ptr_pts_to_uninit $&(p)));
    return read_initialized(&p);
}
