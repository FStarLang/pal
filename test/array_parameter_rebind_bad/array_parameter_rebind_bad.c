#include "pal.h"
#include <stdbool.h>

void fill(_out _array int *a)
  _preserves(a._length == 2)
{
  a[0] = 1;
  a[1] = 2;
}

void bad_retarget(_array int *a, _plain _array int *b, bool replace)
  _requires(a._length == 2)
{
  if (replace) {
    a = b;
    fill(a);
  }
}
