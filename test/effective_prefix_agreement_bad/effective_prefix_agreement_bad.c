#include "pal.h"
#include <stdint.h>

/* A shared prefix and its whole range may have the same address. */
_include_pulse(Prefix_agreement_bad,
  module ET = Pulse.Lib.C.Palow.Etype

  ghost fn bad (a: ptr)
    preserves mem_pts_to_at a 0.5R (zeroed 4) (ET.etypes_of uint32_t_ctype true)
    preserves mem_pts_to_at a 0.5R (slice (zeroed 4) 0 1)
                (FStar.Seq.slice (ET.etypes_of uint32_t_ctype true) 0 1)
    ensures pure False
  {
    mem_pts_to_at_injective a #0.5R #0.5R #(zeroed 4) #(slice (zeroed 4) 0 1) #(ET.etypes_of uint32_t_ctype true) #(FStar.Seq.slice (ET.etypes_of uint32_t_ctype true) 0 1);
  }
)
