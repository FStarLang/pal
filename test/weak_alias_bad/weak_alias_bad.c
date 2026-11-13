#include "pal.h"

#define weak_alias(old, new) \
  extern __typeof(old) new __attribute__((__weak__, __alias__(#old)))

/* The alias is the same code as `__twice`, so it cannot promise more. */
int twice(int x) _requires(x <= 1000 && x >= -1000) _ensures(return == 3 * x);

int __twice(int x)
  _requires(x <= 1000 && x >= -1000)
  _ensures(return == 2 * x)
{
  return x + x;
}

weak_alias(__twice, twice);
