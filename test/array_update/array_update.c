#include "pal.h"
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
