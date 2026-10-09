#include "pal.h"
#include <stddef.h>
#include <stdint.h>

// Loops in functions with struct and array `_out` parameters.

// A loop that fills an `_out` array. The invariant says which cells hold a
// value; together with the exit condition that is every cell.
void zero(_out _array int32_t *a, size_t n)
  _requires(a._length == n)
  _ensures(_forall(size_t j, j < n ==> a[j] == 0))
{
  for (size_t i = 0; i < n; i++)
    _invariant(_live(i) && i <= n)
    _invariant(_forall(size_t j, j < i ==> a[j] == 0))
  {
    a[i] = 0;
  }
}

// The loop reads cells it wrote in earlier iterations.
void iota(_out _array uint32_t *a, size_t n)
  _requires(a._length == n && n >= 1 && n < 1000)
  _ensures(_forall(size_t j, j < n ==> a[j] == j))
{
  a[0] = 0;
  for (size_t i = 1; i < n; i++)
    _invariant(_live(i) && 1 <= i && i <= n)
    _invariant(_forall(size_t j, j < i ==> a[j] == j))
  {
    a[i] = a[i - 1] + 1;
  }
}

// A loop that leaves the `_out` array alone.
void fill_after(_out _array uint8_t *a, uint32_t n)
  _requires(a._length == 1)
  _ensures(a[0] == 7)
{
  uint32_t k = 0;
  while (k < n)
    _invariant(_live(k) && k <= n)
  {
    k = k + 1;
  }
  a[0] = 7;
}

struct point {
  uint32_t x;
  uint32_t y;
};

// A struct `_out` written before the loop, and updated in it.
void count_point(_out struct point *p, uint32_t n)
  _ensures(p->x == n && p->y == 3)
{
  p->x = 0;
  p->y = 3;
  for (uint32_t i = 0; i < n; i++)
    _invariant(_live(i) && _live(*p))
    _invariant(i <= n && p->x == i && p->y == 3)
  {
    p->x = p->x + 1;
  }
}

// A struct `_out` the loop leaves alone, written afterwards.
void point_after(_out struct point *p, uint32_t n)
  _ensures(p->x == n && p->y == 0)
{
  uint32_t acc = 0;
  for (uint32_t i = 0; i < n; i++)
    _invariant(_live(i) && _live(acc))
    _invariant(i <= n && acc == i)
  {
    acc = acc + 1;
  }
  p->x = acc;
  p->y = 0;
}
