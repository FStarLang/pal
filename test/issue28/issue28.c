#include "pal.h"

typedef struct _point {
  int px;
  int py;
} point;

void use_point(point *p)
  _preserves_value(p->py)
  _ensures(p->px == 17)
{
  p->px = 17;
}

void test(void) {
  point p = {.px=0, .py=0};
  use_point(&p);
}