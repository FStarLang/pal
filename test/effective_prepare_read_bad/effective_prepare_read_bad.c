#include "pal.h"
#include <stdint.h>

/* A prepared reservation cannot be used as initialized byte ownership. */
_include_pulse(Prepared_read_bad,
  module Effective = Pulse.Lib.C.Palow.Effective

  ghost
  fn bad (a: ptr)
    requires Effective.prepared a uint32_t_ctype
    ensures exists* b e. mem_pts_to_at a 1.0R b e
  {
    unfold Effective.prepared a uint32_t_ctype;
  }
)
