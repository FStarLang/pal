#include "pal.h"
#include <stdint.h>

/* Equal initialized bytes do not supply an established source effective type. */
_include_pulse(Untyped_copy_bad,
  module EM = Pulse.Lib.C.Palow.Effective.Machine
  module Effective = Pulse.Lib.C.Palow.Effective
  module ET = Pulse.Lib.C.Palow.Etype

  fn bad (dst src: ptr)
    preserves mem_pts_to_at src 0.5R (zeroed 4) (EM.fresh_index 4)
    requires Effective.prepared dst uint32_t_ctype
    ensures mem_pts_to_at dst 1.0R (zeroed 4) (ET.etypes_of uint32_t_ctype false)
  {
    EM.memcpy_prepared dst src 4sz uint32_t_ctype;
  }
)
