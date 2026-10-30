#include "pal.h"

void cannot_claim_initialized(_out int *p, int *q, _Bool write) {
  if (write)
    _ensures((_slprop)_inline_pulse(
      exists* v. int32_t_pts_to $&(*q) 1.0R v))
  {
    *q = 1;
  }
  _assert(_live(p));
  _ghost_stmt(with v. assert int32_t_pts_to $(p) 1.0R v);
  *p = 0;
}
