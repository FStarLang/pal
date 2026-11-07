// With a `_requires`, a loop's `_ensures` has to hold at every `break`.
#include "pal.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

uint32_t find_zero_wrong(_array uint8_t *a, uint32_t n)
  _requires(a._length == n)
{
  uint32_t i = 0;
  bool found = false;
  while (i < n)
    _invariant(_live(i) && _live(found) && i <= n && a._length == n)
    _requires(!found)
    _ensures(found)
  {
    if (a[i] == 0) {
      break;
    }
    i++;
  }
  return i;
}
