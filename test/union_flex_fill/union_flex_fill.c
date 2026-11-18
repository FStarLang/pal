#include "pal.h"
#include <stdint.h>

/* A struct ending in a flexible array member, as a member of a union whose
 * other member fixes its size: the tail fills the union, here with 3 whole
 * elements. */

struct bitmap {
  uint64_t count;
  uint64_t bits[];
};

union bitmap_buf {
  struct bitmap bm;
  uint8_t storage[32];
};

uint64_t bitmap_count(union bitmap_buf *u)
  _requires(u->bm._active)
  _ensures(u->bm._active)
  _ensures(return == u->bm.count)
{
  return u->bm.count;
}

uint64_t last_word(union bitmap_buf *u)
  _requires(u->bm._active)
  _ensures(u->bm._active)
  _ensures(return == u->bm.bits[2])
{
  return u->bm.bits[2];
}

void set_word(union bitmap_buf *u, uint64_t w)
  _requires(u->bm._active)
  _ensures(u->bm._active)
  _ensures(u->bm.bits[1] == w)
  _ensures(u->bm.count == _old(u->bm.count))
{
  u->bm.bits[1] = w;
}

uint8_t first_byte(union bitmap_buf *u)
  _requires(u->storage._active)
  _ensures(u->storage._active)
  _ensures(return == u->storage[0])
{
  return u->storage[0];
}
