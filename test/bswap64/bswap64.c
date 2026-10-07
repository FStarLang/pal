#include "pal.h"
#include <stdint.h>

/* `__builtin_bswap64` in code and in specifications. It is
   `Pulse.Lib.C.UInt64.bswap64`, whose involution lemma is what `twice` and
   `to_be` rely on. */

uint64_t swap(uint64_t x)
  _ensures(return == __builtin_bswap64(x))
{
  return __builtin_bswap64(x);
}

uint64_t twice(uint64_t x)
  _ensures(return == x)
{
  uint64_t y = __builtin_bswap64(x);
  _assert(y == __builtin_bswap64(x));
  return __builtin_bswap64(y);
}

/* Big-endian round trip through a stored value. */
_requires(*p == x)
_ensures(*p == __builtin_bswap64(x))
void to_be(uint64_t *p, uint64_t x) {
  *p = __builtin_bswap64(*p);
  _assert(__builtin_bswap64(*p) == x);
}
