#include "pal.h"

void initialize(_out int *p) {
  *p = 42;
}

void bad_rebind(_out int *p, int *q) {
  p = q;
  initialize(p);
}
