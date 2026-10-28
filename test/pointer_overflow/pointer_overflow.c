#include "pal.h"
#include <stdint.h>

_include_pulse(Pointer_overflow_facts,
  let wraps (a: ptr)
    : Lemma (requires addr_of a == pow2 64 - 1)
            (ensures addr_of (a +! 1sz) == 0)
    = addr_of_add a 1sz

  let ordinary_offset (a: ptr) (n: SizeT.t)
    : Lemma (requires addr_of a + SizeT.v n < pow2 64)
            (ensures addr_of (a +! n) == addr_of a + SizeT.v n)
    = addr_of_add a n

  let alignment_wraps (a: ptr)
    : Lemma (requires addr_of a == pow2 64 - 8)
            (ensures addr_of (a +! 8sz) == 0
                     /\ aligned (a +! 8sz) 8sz)
    = reveal_opaque (`%divides_addr) divides_addr;
      aligned_add a 8sz 8sz

  let arbitrary_alignment_does_not_wrap (a: ptr)
    : Lemma (requires addr_of a == pow2 64 - 1)
            (ensures aligned a 3sz /\ ~(aligned (a +! 3sz) 3sz))
    = reveal_opaque (`%divides_addr) divides_addr;
      addr_of_add a 3sz

  let wrapped_roundtrip (a: ptr)
    : Lemma ((a +! 1sz) -? 1sz == a)
    = add_sub_wrap a 1sz

  ghost fn live_offsets_do_not_wrap (a: ptr) (#p: perm) (#b: bytes)
                                    (n: SizeT.t { SizeT.v n <= len b })
    preserves mem_pts_to a p b
    ensures pure (addr_of (a +! n) == addr_of a + SizeT.v n)
  {
    mem_pts_to_fits a;
    addr_of_add_nowrap a n;
  }
)

void pointer_overflow_facts(_plain _nullable void *p)
{
  _ghost_stmt(Pointer_overflow_facts.wrapped_roundtrip $(p));
}

void local_array_extent(void)
{
  uint32_t values[4];
  _ghost_stmt(assert pure (addr_of $&(values) + 16 < pow2 64));
}
