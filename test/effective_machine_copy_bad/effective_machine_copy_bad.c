#include "pal.h"
#include <stdint.h>

/* A reserved float cannot be initialized by copying an established integer. */
_include_pulse(Effective_copy_bad,
  module EM = Pulse.Lib.C.Palow.Effective.Machine
  module Effective = Pulse.Lib.C.Palow.Effective
  module ET = Pulse.Lib.C.Palow.Etype

  fn bad (dst src: ptr) (#bs: erased bytes)
    preserves mem_pts_to_at src 0.5R bs (ET.etypes_of uint32_t_ctype true)
    requires Effective.prepared dst float32_t_ctype
    requires pure (len bs == 4)
    ensures mem_pts_to_at dst 1.0R bs (ET.etypes_of float32_t_ctype false)
  {
    EM.memcpy_prepared dst src 4sz float32_t_ctype;
  }
)
