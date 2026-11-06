#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

/* `p` takes the address `a` has at the assignment; reassigning `a`
   afterwards does not move `p`. */
int32_t second_of_first(_array int32_t *a, _array int32_t *b)
  _requires(a._length >= 2 && b._length >= 2)
  _ensures(return == a[1])
{
  _array int32_t *p = a;
  a = b;
  return p[1];
}

void write_through_old(_array int32_t *a, _array int32_t *b)
  _requires(a._length >= 2 && b._length >= 2)
  _ensures(a[1] == 7)
{
  _array int32_t *p = a;
  a = b;
  p[1] = 7;
}
