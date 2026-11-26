#include "pal.h"
#include <stddef.h>
#include <stdint.h>

typedef struct { uint32_t lo; uint32_t hi; } desc;

// The declaration's invariant is about ownership: the length of the array the
// iterator owns. It is not a property of the iterator's value alone.
_refine(this.items._length == this.count)
typedef struct _iter {
  _array desc *items;
  uint32_t count;
} iter;

// Embedding the iterator by value carries its invariant into every contract
// that holds an `outer`, at the iterator's ownership inside the outer's.
typedef struct _outer {
  uint32_t tag;
  iter it;
} outer;

typedef struct _nest {
  outer in;
  uint32_t gen;
} nest;

uint32_t outer_first(const outer *o)
{
  if (o->it.count > 0)
    return o->it.items[0].lo;
  return 0;
}

void outer_set_tag(outer *o, uint32_t t)
{
  o->tag = t;
}

uint32_t nest_last(const nest *n)
{
  uint32_t c = n->in.it.count;
  if (c > 0)
    return n->in.it.items[c - 1].hi;
  return 0;
}

uint32_t iter_first(const iter *i)
{
  if (i->count > 0)
    return i->items[0].lo;
  return 0;
}

uint32_t outer_via_iter(const outer *o)
{
  return iter_first(&o->it);
}
