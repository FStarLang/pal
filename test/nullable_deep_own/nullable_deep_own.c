// A `_nullable` pointer to a struct with an `_array` field owns the struct and
// what the field points at, both behind the same nullness guard, and the
// struct's `_refine` holds whenever the pointer is not null.
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
typedef const iter *pciter;

uint32_t citer_count(pciter it)
  _ensures(return == it->count)
{
  return it->count;
}

uint32_t opt_count(_nullable pciter it, uint32_t dflt)
{
  if (it == NULL)
    return dflt;
  return it->count;
}

// A callee that wants the iterator outright gets it, invariant and array
// included, from the side of the test where it is not null.
uint32_t opt_count_call(_nullable pciter it)
{
  uint32_t r = 0;
  if (it != NULL) {
    r = citer_count(it);
  }
  return r;
}

// The invariant is what bounds the read of the array the guard owns.
uint32_t opt_first_lo(_nullable pciter it)
{
  uint32_t r = 0;
  if (it != NULL) {
    if (it->count > 0)
      r = it->items[0].lo;
  }
  return r;
}

// A write to a field the deep ownership does not read leaves it in place.
void opt_rewind(_nullable piter it)
{
  if (it != NULL)
    it->next = 0;
}

uint32_t use_opt(_nullable pciter it)
{
  return opt_count(it, 0) + opt_count_call(it) + opt_first_lo(it);
}
