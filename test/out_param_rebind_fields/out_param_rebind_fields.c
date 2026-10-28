#include "pal.h"

struct pair {
  int x;
  int y;
};

void bad_rebind(_out struct pair *p, struct pair *q) {
  p = q;
  p->x = 1;
  p->y = 2;
}
