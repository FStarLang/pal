#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// Loops. This is the one place where Palow asks the source for something the
// old model did not. Pulse computes the join for an `if` by itself, but no
// system invents a loop invariant, so the invariant has to restate the whole
// ownership frame: one existential per live local and per parameter pointee,
// the points-to that binds it, and only then the proposition the C source
// wrote. `_live(x)` therefore carries no information any more.

uint32_t sum_to(uint32_t n)
  _requires((_specint) n * (n + 1) <= UINT32_MAX)
{
  uint32_t i = 0;
  uint32_t acc = 0;
  while (i < n)
    _invariant(_live(i) && _live(acc))
    _invariant(i <= n)
  {
    i = i + 1;
    acc = acc + i;
  }
  return acc;
}

// A loop that writes through a pointer parameter: the parameter's pointee is
// part of the frame the invariant has to restate, and the invariant names the
// binder the frame introduces rather than the value the contract fixed.
void count_down(uint32_t *p, uint32_t n)
  _requires(*p == n)
{
  uint32_t i = 0;
  while (i < n)
    _invariant(_live(i) && _live(*p))
    _invariant(i <= n)
  {
    *p = *p - 1;
    i = i + 1;
  }
}

// A loop whose body writes an element of an array parameter, which has to focus
// and unfocus inside the loop while the invariant holds the whole sequence.
void zero_all(uint32_t a[], size_t n)
  _requires(a._length == n)
  _preserves_value(a._length)
{
  size_t i = 0;
  while (i < n)
    _invariant(_live(i) && _live(*a))
    _invariant(a._length == n && i <= n)
  {
    a[i] = 0;
    i = i + 1;
  }
}

uint32_t iteration_scratch(uint32_t n)
  _ensures(return == n)
{
  uint32_t i = 0;
  uint32_t temporary;
  while (i < n)
    _invariant(i <= n)
  {
    temporary = i;
    i = temporary + 1;
  }
  return i;
}

union scratch_word {
  uint32_t value;
  uint32_t bits;
};

uint32_t scratch_jumps(uint32_t n, uint32_t stop, uint32_t skip)
  _ensures(return <= n)
{
  uint32_t i = 0;
  union scratch_word temporary;
  while (i < n)
    _invariant(i <= n)
    _ensures(i <= n)
  {
    temporary.value = i;
    if (i == stop) {
      break;
    }
    if (i == skip) {
      i = i + 1;
      continue;
    }
    _assert(temporary.value == i);
    i = temporary.value + 1;
  }
  temporary.value = i;
  return temporary.value;
}

uint32_t nested_scratch(uint32_t n)
  _ensures(return == n)
{
  uint32_t i = 0;
  uint32_t temporary;
  while (i < n)
    _invariant(i <= n)
  {
    uint32_t j = 0;
    while (j < 1)
      _invariant(j <= 1)
      _invariant(i < n)
    {
      temporary = i;
      _assert(temporary == i);
      j = j + 1;
    }
    i = i + 1;
  }
  return i;
}
