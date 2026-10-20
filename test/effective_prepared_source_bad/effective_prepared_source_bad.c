#include "pal.h"
#include <stdint.h>

/* A prepared source cannot be exposed even for a declared destination copy. */
_include_pulse(Prepared_source_bad,
  module EM = Pulse.Lib.C.Palow.Effective.Machine
  module Effective = Pulse.Lib.C.Palow.Effective
  module ET = Pulse.Lib.C.Palow.Etype

  fn bad (dst src: ptr)
    preserves Effective.prepared src uint32_t_ctype
    requires mem_pts_to_at dst 1.0R (zeroed 4) (ET.etypes_of float32_t_ctype true)
    ensures mem_pts_to_at dst 1.0R (zeroed 4) (ET.etypes_of float32_t_ctype true)
  {
    EM.memcpy dst src 4sz #0.5R #(zeroed 4) #(zeroed 4) #(ET.etypes_of float32_t_ctype true) #(ET.etypes_of uint32_t_ctype true);
  }
)
