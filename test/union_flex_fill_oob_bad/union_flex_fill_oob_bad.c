#include "pal.h"
#include <stdint.h>

struct bitmap {
  uint64_t count;
  uint64_t bits[];
};

union bitmap_buf {
  struct bitmap bm;
  uint8_t storage[32];
};

/* The 32-byte union leaves room for 3 elements of the tail, so `bits[3]` is
 * out of bounds, though the union is all the tail could be. */
uint64_t past_end(union bitmap_buf *u)
  _requires(u->bm._active)
  _ensures(u->bm._active)
{
  return u->bm.bits[3];
}
