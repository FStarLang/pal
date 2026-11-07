#include "pal.h"
#include <stddef.h>
#include <stdint.h>

uint32_t read_without_bound(_plain _array const uint32_t *a, size_t i)
  _preserves(_inline_pulse(
    array_pts_to uint32_t_repr 4 (SizeT.v uint32_t_alignof) $(a) 0.5R $`values))
{
  return a[i];
}
