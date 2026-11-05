#include "pal.h"
#include <stddef.h>
#include <stdint.h>

void write_readonly(_plain _array uint32_t *a, size_t i)
  _preserves(_inline_pulse(
    array_pts_to uint32_t_repr 4 (SizeT.v uint32_t_alignof) $(a) 0.5R $`values **
    pure (SizeT.v $(i) < Seq.length $`values)))
{
  a[i] = 7;
}
