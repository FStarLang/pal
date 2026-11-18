#include "pal.h"
#include <stddef.h>
#include <stdint.h>

// A shift count of 2^32 is out of range for every width, so the shift
// is not defined. Narrowing the count to `uint32_t` by truncation would make it
// 0 and the shift an identity.

size_t sz_shift(size_t a, size_t s)
  _requires(s == 4294967296)
  _ensures(return == a)
{
  return a << s;
}
