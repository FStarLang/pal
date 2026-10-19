#include "pal.h"
#include <stdint.h>

/* A declared object's origin cannot be forgotten to obtain retypability. */
_include_pulse(Prepared_fixed_bad,
  module Effective = Pulse.Lib.C.Palow.Effective

  ghost
  fn bad (a: ptr)
    requires mem_pts_to_at a 1.0R (uninit 4) (ET.etypes_of uint32_t_ctype true)
    ensures Effective.prepared a uint32_t_ctype
  {
    Effective.prepare a uint32_t_ctype;
  }
)
