#include "pal.h"
#include <stddef.h>
#include <stdint.h>

// The example from issue #350: a conditional whose arms are plain values.
uint8_t link_bit(uint8_t nsr)
  _ensures(return <= 1)
{
  uint8_t masked = nsr & 0x40;
  return masked ? 1 : 0;
}

uint32_t clamp(uint32_t a, uint32_t b)
  _ensures(return <= a && return <= b)
{
  return a < b ? a : b;
}

// Only the arm taken is evaluated: the read is out of bounds when n == 0.
uint32_t last_or_zero(_array uint32_t *a, size_t n)
  _requires(a._length == n)
  _ensures(n == 0 ==> return == 0)
{
  return n > 0 ? a[n - 1] : 0;
}

uint32_t twice(uint32_t x)
  _requires(x < 1000)
  _ensures(return == 2 * x)
{
  return x + x;
}

// A call in one arm, whose precondition holds only on that arm.
uint32_t pick(uint32_t c, uint32_t x)
  _ensures(c == 0 ==> return == x)
{
  uint32_t r = c && x < 1000 ? twice(x) : x;
  return r;
}

uint32_t pick_return(uint32_t c, uint32_t x)
  _requires(x < 1000)
  _ensures(c != 0 ==> return == 2 * x)
{
  return c ? twice(x) : x;
}

// A conditional nested inside a larger expression and as a call argument.
uint32_t nested(uint32_t c, uint32_t x)
  _requires(x < 100)
  _ensures(c == 0 ==> return == 2 * x + 1)
{
  uint32_t y = (c ? 0 : twice(x)) + 1;
  return twice(c ? 0 : x) + 1;
}

// `&&` and `||` evaluate their right side only when the left does not decide.
_Bool last_is_zero(_array uint32_t *a, size_t n)
  _requires(a._length == n)
  _ensures(n == 0 ==> !return)
{
  return n > 0 && a[n - 1] == 0;
}

_Bool empty_or_first_zero(_array uint32_t *a, size_t n)
  _requires(a._length == n)
  _ensures(n == 0 ==> return)
{
  return n == 0 || a[0] == 0;
}
