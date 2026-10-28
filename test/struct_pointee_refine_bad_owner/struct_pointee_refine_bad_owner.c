#include "pal.h"

struct _refine(_inline_pulse(int32_t_pts_to $(this.cell) 1.0R $(this.x))) owned {
  int x;
  _plain int *cell;
};

void lose_owner(struct owned *p, _plain int *other) {
  p->cell = other;
}
