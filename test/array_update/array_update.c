#include "pal.h"
#include <stdint.h>

struct point {
    int x;
    int y;
};

void set_x(struct point arr[])
    _requires(arr._length == 2)
{
    arr[0].x = 42;
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