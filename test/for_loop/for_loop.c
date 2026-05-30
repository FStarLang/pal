#include "pal.h"
#include <stdint.h>

/* Multiply by repeated addition, using a for-loop. */
uint32_t multiply_for(uint32_t x, uint32_t y)
  _requires((_specint) x * y <= UINT32_MAX)
  _ensures(return == x * y)
{
  uint32_t acc = 0;
  for (uint32_t ctr = 0; ctr < x; ctr = ctr + 1)
    _invariant(_live(ctr) && _live(acc))
    _invariant(ctr <= x && acc == ctr * y)
  {
    acc = acc + y;
  }
  return acc;
}

/* Count elements, skipping one index — tests continue in for-loop. */
uint32_t count_skip(uint32_t n, uint32_t skip)
{
  uint32_t count = 0;
  for (uint32_t i = 0; i < n; i = i + 1)
    _invariant(_live(i) && _live(count))
    _invariant(i <= n)
    _invariant(count <= i)
  {
    if (i == skip) {
      continue;
    }
    count = count + 1;
  }
  return count;
}
