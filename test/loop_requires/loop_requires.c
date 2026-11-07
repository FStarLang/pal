// A loop's `_requires` holds at the head of every iteration but not at a
// `break`; its `_ensures` is what a `break` establishes. After the loop,
// either the loop ran out with `_requires` and the condition false, or it
// broke out with `_ensures`.
#include "pal.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

uint32_t find_zero(_array uint8_t *a, uint32_t n)
  _requires(a._length == n)
  _ensures(return <= n)
{
  uint32_t i = 0;
  bool found = false;
  while (i < n)
    _invariant(_live(i) && _live(found) && i <= n && a._length == n)
    _requires(!found)
    _ensures(found && i < n)
  {
    if (a[i] == 0) {
      found = true;
      break;
    }
    i++;
  }
  if (found) {
    _assert(i < n);
  } else {
    _assert(!found && i == n);
  }
  return i;
}

// The shape of a batched loop that hands the rest of its work on: the batch
// bound holds while looping, and the hand-off flag is set only on the way out.
void batch(uint32_t *done, bool *more, uint32_t n)
  _requires(*done == 0 && !*more)
  _ensures(*more || *done <= 8)
{
  uint32_t k = 0;
  while (k < n)
    _invariant(_live(k) && k <= n)
    _requires(*done <= 8 && !*more)
    _ensures(*more && *done == 8)
  {
    if (*done == 8) {
      *more = true;
      break;
    }
    *done = *done + 1;
    k++;
  }
  if (*more) {
    _assert(*done == 8);
  } else {
    _assert(k == n && *done <= 8);
  }
}

// Without a `break` the `_ensures` is never established, and what the loop
// leaves behind is its `_requires` and the negated condition.
uint32_t count_up(uint32_t n)
  _requires(n <= 100)
  _ensures(return == n)
{
  uint32_t i = 0;
  uint32_t s = 0;
  while (i < n)
    _invariant(_live(i) && _live(s) && i <= n)
    _requires(s == i)
    _ensures(false)
  {
    s++;
    i++;
  }
  return s;
}
