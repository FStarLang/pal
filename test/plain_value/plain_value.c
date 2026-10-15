#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// `_plain` on a value parameter takes the bare value: the ownership that
// the struct's pointer fields would carry, and the struct- and field-level
// `_refine`s of its type, are not part of the contract.

typedef _refine(this.len <= 16) struct buf { uint32_t len; int32_t *data; } buf;
struct pr { _refine(this < 10) uint32_t small; int32_t *p; };

uint64_t id(_plain uint64_t x)
  _ensures(return == x)
{ return x; }

uint32_t get_len(_plain buf b)
  _ensures(return == b.len)
{ return b.len; }

uint32_t get_small(_plain struct pr s)
  _ensures(return == s.small)
{ return s.small; }

_Bool is_null(_plain struct pr s)
{ return s.p == NULL; }

// A refinement written on the parameter itself is still stated.
uint32_t below5(_refine(this < 5) _plain uint32_t x)
  _ensures(return < 5)
{ return x; }

// Without `_plain` the field's refinement is known, and the caller can hand
// its value to a `_plain` parameter while keeping the ownership.
uint32_t caller(struct pr s)
  _ensures(return < 10)
{
  uint32_t r = get_small(s);
  return r;
}

// A `_plain` struct needs no ownership: a local with a null pointer will do.
// (A pure field `_refine` is part of the record type itself, so the value
// still has to satisfy it.)
uint32_t make(void)
  _ensures(return == 7)
{
  struct pr s;
  s.small = 7;
  s.p = NULL;
  return get_small(s);
}
