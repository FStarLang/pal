#include "pal.h"
#include <stddef.h>
#include <stdint.h>

// A null test on a `_nullable` parameter opens its guard: the arm where the
// pointer is not null owns the pointee.

uint32_t read_or_zero(_nullable uint32_t *p)
  _ensures(p == NULL ==> return == 0)
{
  if (p != NULL) return *p;
  return 0;
}

uint32_t read_or_zero_cond(_nullable const uint32_t *p)
  _ensures(p == NULL ==> return == 0)
{
  return p ? *p : 0;
}

void set_if(_nullable uint32_t *p)
{
  if (p) *p = 5;
}

void set_unless_null(_nullable uint32_t *p)
{
  if (p == NULL) {
    return;
  }
  *p = 7;
}

void bump(uint32_t *p)
  _requires(*p < 100)
  _ensures(*p == _old(*p) + 1)
{
  *p = *p + 1;
}

void bump_if(_nullable uint32_t *p)
{
  if (!p) return;
  if (*p < 100) bump(p);
}

struct pt { int32_t x; int32_t y; };

int32_t get_x(_nullable const struct pt *q)
{
  if (q) return q->x;
  return -1;
}

void set_both(_nullable uint32_t *p)
{
  set_if(p);
  if (p) *p = 1;
  set_if(p);
}

// Inside an expression: the arm, or the right side, where the pointer is not
// null opens the guard and closes it again.
uint32_t add_or_zero(_nullable const uint32_t *p, uint32_t x)
  _requires(x < 100)
{
  uint32_t r = (p ? *p % 100 : 0) + x;
  return r;
}

_Bool is_big(_nullable const uint32_t *p)
  _ensures(p == NULL ==> !return)
{
  return p && *p > 3;
}

_Bool null_or_zero(_nullable const uint32_t *p)
  _ensures(p == NULL ==> return)
{
  if (p == NULL || *p == 0) return 1;
  return 0;
}
