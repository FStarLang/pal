#include "pal.h"
#include <stdint.h>

// Struct field access. Under Palow a struct's points-to is the separating
// conjunction of its fields', so `s->f` is a focus of one field, a machine
// operation on it, and an unfocus -- the same shape as an array subscript,
// because it is the same operation on a sub-range.

struct point {
  int32_t x;
  int32_t y;
};

int32_t get_x(const struct point *p)
  _ensures(return == p->x)
{
  return p->x;
}

void set_x(struct point *p, int32_t v)
  _ensures(p->x == v && p->y == _old(p->y))
{
  p->x = v;
}

// Two fields of the same struct, in both directions. An unfocus that put the
// wrong field back, or forgot to rebuild the record, shows up here.
void swap_xy(struct point *p)
  _ensures(p->x == _old(p->y) && p->y == _old(p->x))
{
  int32_t t = p->x;
  p->x = p->y;
  p->y = t;
}

// A struct whose fields are of different widths, so the offsets are not all
// multiples of one size and padding is possible.
struct mixed {
  uint8_t tag;
  uint64_t value;
};

void bump(struct mixed *m, uint8_t t)
  _ensures(m->tag == t)
{
  m->tag = t;
}

// Two structs at once: focusing a field of one must not disturb the other.
void copy_point(struct point *a, const struct point *b)
  _ensures(a->x == b->x && a->y == b->y)
{
  a->x = b->x;
  a->y = b->y;
}
