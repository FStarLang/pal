// A `_refine` on a typedef'd struct is that struct's invariant. A pointer to
// it held in another struct's field is an address; the invariant is not a
// relation between the outer struct's fields.
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

typedef iter *piter;

typedef struct {
  piter it;
  uint32_t total;
} message;

typedef struct {
  _plain piter it;
  uint32_t total;
} plain_message;

uint32_t message_total(message *m)
  _ensures(return == m->total)
{
  return m->total;
}

void set_total(plain_message *m, uint32_t t)
  _ensures(m->total == t)
{
  m->total = t;
}

uint32_t iter_count(piter it)
  _ensures(return == it->count)
{
  return it->count;
}

// The pointee's invariant is what bounds the read.
uint32_t first_lo(piter it)
  _requires(it->count > 0)
{
  return it->items[0].lo;
}
