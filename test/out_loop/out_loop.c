#include "pal.h"
#include <stdint.h>

// Loops in functions with `_out` parameters (issue #347).

// The loop updates the `_out` storage after it has been written.
void count_out(_out uint32_t *res, uint32_t n)
  _ensures(*res == n)
{
  uint32_t i = 0;
  *res = 0;
  while (i < n)
    _invariant(_live(i) && _live(*res))
    _invariant(i <= n && *res == i)
  {
    *res = *res + 1;
    i = i + 1;
  }
}

// The loop leaves the `_out` storage alone; it is written afterwards.
void sum_out(_out uint64_t *res, uint32_t n)
  _ensures(*res == n)
{
  uint64_t acc = 0;
  for (uint32_t i = 0; i < n; i++)
    _invariant(_live(i) && _live(acc))
    _invariant(i <= n && acc == i)
  {
    acc = acc + 1;
  }
  *res = acc;
}

// Two outputs: one written before the loop, one after.
void two_out(_out uint32_t *a, _out uint32_t *b, uint32_t n)
  _ensures(*a == n && *b == 7)
{
  *a = 0;
  for (uint32_t i = 0; i < n; i++)
    _invariant(_live(i) && _live(*a))
    _invariant(i <= n && *a == i)
  {
    *a = *a + 1;
  }
  *b = 7;
}
