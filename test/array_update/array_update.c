#include "pal.h"
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

struct point {
    int x;
    int y;
};

void set_x_alt(struct point arr[])
    _requires(arr._length == 2)
{
    arr[0].x = 42;
}


void set_x(_array struct point *pts, size_t i, int val)
  _requires(i < pts._length)
  _preserves_value(pts._length)
  _ensures(pts[i].x == val)
{
  pts[i].x = val;
}

void set_y(_array struct point *pts, size_t i, int val)
  _requires(i < pts._length)
  _preserves_value(pts._length)
  _ensures(pts[i].y == val)
{
  pts[i].y = val;
}

void set_both(_array struct point *pts, size_t i, int vx, int vy)
  _requires(i < pts._length)
  _preserves_value(pts._length)
  _ensures(pts[i].x == vx)
  _ensures(pts[i].y == vy)
{
  pts[i].x = vx;
  pts[i].y = vy;
}

struct entry {
    uint64_t value;
    uint64_t time;
};


void set_elem_fields(_array struct entry *a, uint32_t i, uint64_t v, uint64_t t)
  _requires((size_t)i < a._length)
  _preserves_value(a._length)
  _ensures(a[i].value == v && a[i].time == t)
{
    a[i].value = v;
    a[i].time = t;
}

// Like set_x, but instead of taking the whole array it takes an _arrayptr that
// already points at the struct to update. The field is written through the
// pointer (p->x), borrowing write permission from the parent array `arr`.
// An interior pointer is an address like any other here, and there is no
// separate `arrayptr` predicate relating it to the array it came out of: what
// the caller lends is a run of cells starting at this address, which it split
// off and will put back. So the Palow contract is the ordinary array one, and
// the only thing it has to say is that the run is not empty.
void set_x_via_ptr(_array struct point *p, int val)
  _requires(p._length > 0)
{
  p->x = val;
}

void rebind_array_local(_array struct point *a, _array struct point *b)
  _requires(a._length > 0 && b._length > 0)
  _preserves_value(a._length)
  _preserves_value(b._length)
  _ensures(a[0].x == 10 && b[0].x == 20)
{
  _array struct point *p = NULL;
  p = a;
  p[0].x = 10;
  p = b;
  p[0].x = 20;
}

union point_array {
  _array struct point *points;
  uintptr_t bits;
};

void read_union_array(_array struct point *a)
  _requires(a._length > 0)
  _preserves_value(a._length)
  _ensures(a[0].x == 42)
{
  union point_array u;
  u.points = a;
  u.points[0].x = 42;
}

_plain uint32_t *array_address(_plain _array uint32_t *a, uint32_t i)
  _ensures(_inline_pulse(
    pure ($(return) == $(a) +! (4sz `SizeT.mul` (sizet_of_uint32 $(i))))))
{
  return &a[i];
}

_plain struct point *union_array_address(_plain _array struct point *a, uint32_t i)
  _ensures(_inline_pulse(
    pure ($(return) == $(a) +! (8sz `SizeT.mul` (sizet_of_uint32 $(i))))))
{
  union point_array u;
  u.points = a;
  return &u.points[i];
}

bool uninitialized_array_end(void)
  _ensures(return == true)
{
  uint32_t a[4];
  _plain uint32_t *end = &a[4];
  return end == &a[4];
}

uint64_t read_entry(const struct entry *e)
  _ensures(return == e->value)
{
  return e->value;
}

uint64_t read_index(_array struct entry *a, uint32_t i)
  _requires(i < a._length)
  _ensures(return == a[i].value)
{
  return read_entry(&a[i]);
}

uint64_t read_index_alias(_array struct entry *a, uint32_t i)
  _requires(i < a._length)
  _ensures(return == a[i].value)
{
  const struct entry *e = &a[i];
  return read_entry(e);
}

uint64_t read_index_callback(_array struct entry *a, uint32_t i)
  _requires(i < a._length)
  _ensures(return == a[i].value)
{
  uint64_t (*read)(const struct entry *) = read_entry;
  return read(&a[i]);
}
