#include "pal.h"

/* A negative test.  Verification of this file is *expected to fail*, and the
   `should-fail` marker next to it names the message that has to appear; that
   is how we check that Palow's alignment discipline actually bites rather
   than being a clause nothing ever reads.

   Four bytes are four bytes wherever they sit, but a `uint32_t` object may
   only live at an address divisible by four.  One byte past a maximally
   aligned address never is, so the claim below cannot go through. */

_include_pulse(M,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  include Pulse.Lib.C.Palow.Scalar
  include Pulse.Lib.C.Palow.Index
  module ET = Pulse.Lib.C.Palow.Etype

  ghost fn claim_misaligned (a: ptr) (#b: bytes) (#e: ET.etypes)
    requires mem_pts_to_at (a +! 1sz) 1.0R b e
    requires pure (aligned a max_align)
    requires pure (len b == FStar.SizeT.v uint32_t_sizeof)
    requires pure (ET.elen e == len b /\ ET.untyped e)
    ensures  uint32_t_pts_to_uninit (a +! 1sz)
  {
    uint32_t_etype_ok_untyped e;
    uint32_t_claim_uninit (a +! 1sz);
  }
)

void misaligned(void)
{
}
