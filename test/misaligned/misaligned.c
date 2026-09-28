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

  ghost fn claim_misaligned (a: ptr) (#b: bytes)
    requires mem_pts_to (a +! 1sz) 1.0R b
    requires pure (aligned a max_align)
    requires pure (len b == FStar.SizeT.v uint32_t_sizeof)
    ensures  uint32_t_pts_to_uninit (a +! 1sz)
  {
    uint32_t_claim_uninit (a +! 1sz);
  }
)

void misaligned(void)
{
}
