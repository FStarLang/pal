#include "pal.h"
#include <stdint.h>
#include <stddef.h>

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

// A fixed-size array field. In C `T f[N]` inside a struct is N elements of
// storage, not a pointer, so the field owns a whole `array_pts_to` and its
// length is part of the record type. A subscript through one focuses the field
// out of the struct and then the element out of the field.
struct buf {
  uint32_t len;
  uint32_t data[4];
};

uint32_t first(const struct buf *b)
  _ensures(return == b->data[0])
{
  return b->data[0];
}

void store(struct buf *b, size_t i, uint32_t v)
  _requires(i < 4)
  _ensures(b->data[i] == v)
{
  b->data[i] = v;
}

// A scalar field and an array field of the same struct, in one function.
void set_len(struct buf *b, uint32_t v)
  _ensures(b->len == v && b->data[0] == _old(b->data[0]))
{
  b->len = v;
}
