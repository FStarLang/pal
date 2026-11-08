#include "pal.h"

void *read_initialized(_plain void **p)
  _ghost_arg(void *Value)
  _preserves(_inline_pulse(Pulse.Lib.C.Palow.Scalar.ptr_pts_to $(p) 1.0R $(Value)))
{
    return *p;
}

void *read_unwritten(_plain void **p)
  _requires(_inline_pulse(Pulse.Lib.C.Palow.Scalar.ptr_pts_to_uninit $(p)))
  _ensures(_inline_pulse(Pulse.Lib.C.Palow.Scalar.ptr_pts_to_uninit $(p)))
{
    return read_initialized(p);
}
