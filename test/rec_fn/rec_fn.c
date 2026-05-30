#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

/* Pure recursive function: sum 0..n with decreases clause */
_rec _pure uint32_t sum_to(uint32_t n)
  _requires((_specint) n * ((_specint) n + 1) / 2 <= UINT32_MAX)
  _ensures((_specint) return == (_specint) n * ((_specint) n + 1) / 2)
  _decreases((_specint) n)
{
  if (n == 0) {
    return 0;
  } else {
    return n + sum_to(n - 1);
  }
}

/* Recursive Pulse function: fill a[lo..hi) with val, proving frame preservation */
_rec void fill(_array uint32_t *a, size_t len, size_t lo, size_t hi, uint32_t val)
  _requires(a._length == len)
  _requires(lo <= hi && hi <= len)
  _preserves_value(a._length)
  _ensures(_forall(size_t k, lo <= k && k < hi ==> a[k] == val))
  _ensures(_forall(size_t k, k < len && (k < lo || k >= hi) ==> a[k] == _old(a[k])))
  _decreases(hi - lo)
{
  if (lo >= hi) {
    return;
  }
  a[lo] = val;
  fill(a, len, lo + 1, hi, val);
}

/* Recursive Pulse function: zero out a[i..len) using simple count-down */
_rec void zero_from(_array uint32_t *a, size_t len, size_t i)
  _requires(a._length == len)
  _requires(i <= len)
  _preserves_value(a._length)
  _ensures(_forall(size_t k, i <= k && k < len ==> a[k] == 0))
  _ensures(_forall(size_t k, k < i ==> a[k] == _old(a[k])))
  _decreases(len - i)
{
  if (i >= len) return;
  a[i] = 0;
  zero_from(a, len, i + 1);
}

/* Caller that uses both recursive functions */
void test(_array uint32_t *a, size_t len)
  _requires(a._length == len)
  _requires(len >= 1)
  _preserves_value(a._length)
  _ensures(_forall(size_t k, k < len ==> a[k] == 0))
{
  fill(a, len, 0, len, 42);
  zero_from(a, len, 0);
}
