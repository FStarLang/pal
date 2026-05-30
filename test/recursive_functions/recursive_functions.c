// Recursive functions: _rec and _decreases annotations

#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

// Pure recursive function with _decreases annotation
_rec _pure int recursive_sum(int x, int limit)
    _requires(0 <= x && x <= limit)
    _requires((_specint) limit * 12 <= INT32_MAX)
    _ensures((_specint) return == ((_specint) limit - (_specint) x) * 12)
    _decreases((_specint) limit - (_specint) x)
{
    if (x >= limit) return 0;
    else return 12 + recursive_sum(x + 1, limit);
}

// Impure recursive function: fill a[lo..hi) with val
_rec void fill(_array uint32_t *a, size_t len, size_t lo, size_t hi, uint32_t val)
    _requires(a._length == len)
    _requires(lo <= hi && hi <= len)
    _preserves_value(a._length)
    _ensures(_forall(size_t k, lo <= k && k < hi ==> a[k] == val))
    _ensures(_forall(size_t k, k < len && (k < lo || k >= hi) ==> a[k] == _old(a[k])))
    _decreases(hi - lo)
{
    if (lo >= hi) return;
    a[lo] = val;
    fill(a, len, lo + 1, hi, val);
}
