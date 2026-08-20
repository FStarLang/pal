#include "pal.h"
#include <stdint.h>

// Test: ++/-- (pre or post) applied to an _arrayptr pointer, differentiating
// pre from post by capturing the expression's own return value: post returns
// the OLD position, pre returns the NEW position (same as p after the op).

int32_t post_incr(_array int32_t *a)
  _requires(a._length == 4)
  _preserves_value(a._length)
  _ensures(return == 1)
{
  _arrayptr int32_t *p = a;
  _arrayptr int32_t *q = p++;
  int32_t result = (q < p) ? 1 : 0;
  _ghost_stmt(arrayptr_drop $(p));
  _ghost_stmt(arrayptr_drop $(q));
  return result;
}

int32_t pre_incr(_array int32_t *a)
  _requires(a._length == 4)
  _preserves_value(a._length)
  _ensures(return == 1)
{
  _arrayptr int32_t *p = a;
  _arrayptr int32_t *q = ++p;
  int32_t result = (q == p) ? 1 : 0;
  _ghost_stmt(arrayptr_drop $(p));
  _ghost_stmt(arrayptr_drop $(q));
  return result;
}

int32_t post_decr(_array int32_t *a)
  _requires(a._length == 4)
  _preserves_value(a._length)
  _ensures(return == 1)
{
  _arrayptr int32_t *p = a + 1;
  _arrayptr int32_t *q = p--;
  int32_t result = (p < q) ? 1 : 0;
  _ghost_stmt(arrayptr_drop $(p));
  _ghost_stmt(arrayptr_drop $(q));
  return result;
}

int32_t pre_decr(_array int32_t *a)
  _requires(a._length == 4)
  _preserves_value(a._length)
  _ensures(return == 1)
{
  _arrayptr int32_t *p = a + 1;
  _arrayptr int32_t *q = --p;
  int32_t result = (q == p) ? 1 : 0;
  _ghost_stmt(arrayptr_drop $(p));
  _ghost_stmt(arrayptr_drop $(q));
  return result;
}
