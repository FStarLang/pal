#include "../../examples/pal.h"
#include <stdint.h>

void select_tail(
    _array uint8_t *bytes,
    uint32_t off,
    _arrayptr uint8_t **out)
  _requires(_inline_pulse(array_pts_to_full $(bytes) $`p_bytes_0 $`val_bytes_0))
  _requires(off <= bytes._length)
  _requires(_inline_pulse(Pulse.Lib.Reference.pts_to_uninit $(out)))
  _ensures(_inline_pulse(array_pts_to_full $(bytes) $`p_bytes_0 $`val_bytes_0))
  _ensures(_inline_pulse(exists* (p: array Typedef_uint8_t.ty_uint8_t). Pulse.Lib.Reference.pts_to $(out) p ** arrayptr_pts_to p $(bytes)))
{
    *out = bytes + off;
}
