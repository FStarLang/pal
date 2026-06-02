#include "pal.h"

struct _pulse_eager_unfold_predicate point {
  int x;
  int y;
};

void set_x(struct point *p, int v)
  _ensures(p->x == v)
{
  p->x = v;
}
