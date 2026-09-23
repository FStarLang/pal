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
    // Palow's array ownership does not carry the length, so the invariant has
    // to say it: nothing in the loop changes it, but the loop is where the
    // ownership is re-stated.
    _invariant(a._length == len && b._length == len)
    _invariant(_forall(size_t j, j < i ==> a[j] == b[j]))
  {
    if (a[i] != b[i]) return false;
  }
  return true;
}