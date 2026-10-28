#include "pal.h"

void bad_rebind(_out int *p, int *q) {
  p = q;
  *p = 42;
}
