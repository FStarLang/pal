#include "pal.h"
#include <stdbool.h>
#include <stddef.h>

bool compare_elems(_array int *a, _array int *b, size_t len)
  _requires(a._length == len && b._length == len)
  _preserves_value(a._length)
  _preserves_value(b._length)
  _ensures(return == _forall(size_t i, i < len ==> a[i] == b[i]))
{
  size_t i = 0;
  while (i < len)
    _invariant(_live(i))
    _invariant(i <= len)
    _invariant(_forall(size_t j, j < i ==> a[j] == b[j]))
  {
    if (a[i] != b[i]) return false;
  }
  return true;
}