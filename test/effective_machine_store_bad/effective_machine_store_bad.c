#include "pal.h"
#include <stdint.h>

/* Reinterpreting an existing object's bytes is not a typed float store. */
_include_pulse(Effective_store_bad,
  module EM = Pulse.Lib.C.Palow.Effective.Machine
  module ET = Pulse.Lib.C.Palow.Etype

  fn bad (a: ptr)
    requires mem_pts_to_at a 1.0R (zeroed 4)
               (ET.etypes_of uint32_t_ctype true)
    ensures mem_pts_to_at a 1.0R (zeroed 4)
               (ET.etypes_of float32_t_ctype true)
  {
    EM.store a float32_t_ctype (zeroed 4);
  }
)
