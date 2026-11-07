#include "pal.h"
#include <stdint.h>

struct _refine(_inline_pulse(int32_t_pts_to $(this.cell) 1.0R $(this.x))) owned {
  int x;
  _plain int *cell;
};

struct box {
  struct owned value;
};

struct outer {
  struct box inner;
};

void lose_nested_owner(struct outer *p, _plain int *other) {
  p->inner.value.cell = other;
}
