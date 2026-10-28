#include "pal.h"

void cannot_claim_initialized(_out int *p) {
  _assert(_live(p));
  _ghost_stmt(with v. assert int32_t_pts_to $(p) 1.0R v);
  *p = 0;
}
