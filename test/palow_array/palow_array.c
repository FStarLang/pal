#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// Subscripts through an array parameter. Under Palow an array parameter owns a
// sequence rather than a single value, so `a[i]` is not a read: it is
// `array_focus`, a machine operation on the one element, and `array_unfocus`.
// These cases exist to pin that translation down for reads, for writes, and for
// the two together.

uint32_t get(uint32_t a[], size_t i, size_t n)
  _requires(a._length == n && i < n)
  _preserves_value(a._length)
  _ensures(return == a[i])
{
  return a[i];
}

void set(uint32_t a[], size_t i, size_t n, uint32_t v)
  _requires(a._length == n && i < n)
  _preserves_value(a._length)
  _ensures(a[i] == v)
{
  a[i] = v;
}

// A read and a write through the same array, which is where an unfocus that
// forgot to put the element back would show up.
void copy_cell(uint32_t a[], size_t i, size_t j, size_t n)
  _requires(a._length == n && i < n && j < n)
  _preserves_value(a._length)
  _ensures(a[i] == _old(a[j]))
{
  a[i] = a[j];
}

// Two arrays at once: the focus of one must not disturb the other.
void add_into(uint32_t a[], const uint32_t b[], size_t i, size_t n)
  _requires(a._length == n && b._length == n && i < n)
  _preserves_value(a._length)
{
  a[i] = a[i] + b[i];
}
