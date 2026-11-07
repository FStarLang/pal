// The invariant of a `_nullable` iterator bounds its array at `count`
// elements; reading the element at `count` is out of bounds.
#include "pal.h"
#include <stddef.h>
#include <stdint.h>

typedef struct {
  uint32_t lo;
  uint32_t hi;
} desc;

_refine(this.items._length == this.count)
typedef struct _iter {
  _array desc *items;
  uint32_t count;
  uint32_t next;
} iter;

typedef const iter *pciter;

uint32_t opt_past_end(_nullable pciter it)
{
  uint32_t r = 0;
  if (it != NULL) {
    r = it->items[it->count].lo;
  }
  return r;
}
