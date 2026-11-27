#include "pal.h"
#include <stddef.h>
#include <stdint.h>

// Seven writes to one object, each to a different field. After each write the
// object's value is the previous one with one field replaced, so the checker
// sees a chain of seven updates of a seven-field struct; the size of that
// chain's term, and the time to check it, must stay linear in its length.
struct desc {
    uint64_t f0, f1, f2, f3, f4, f5, f6;
};

void fill_one(struct desc *p, uint64_t v)
  _ensures(p->f0 == v)
  _ensures(p->f3 == v)
  _ensures(p->f6 == v)
{
    p->f0 = v;
    p->f1 = v;
    p->f2 = v;
    p->f3 = v;
    p->f4 = v;
    p->f5 = v;
    p->f6 = v;
}

void fill_elem(_array struct desc *a, size_t i, uint64_t v)
  _requires(i < a._length)
  _preserves_value(a._length)
  _ensures(a[i].f0 == v)
  _ensures(a[i].f6 == v)
{
    a[i].f0 = v;
    a[i].f1 = v;
    a[i].f2 = v;
    a[i].f3 = v;
    a[i].f4 = v;
    a[i].f5 = v;
    a[i].f6 = v;
}
