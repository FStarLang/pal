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

// A local array. Its elements are written one at a time, so ownership of one
// is an `array_pts_to` whose elements are `option`s: `None` represents any
// bytes of the right width, and every combinator above applies to it
// unchanged. Reading an element needs it to be a `Some`, which is C's rule
// that reading an uninitialised object is undefined -- as an obligation on the
// generated code rather than a restriction on what can be translated.
uint32_t local_array()
  _ensures(return == 7)
{
  uint32_t buf[4];
  buf[1] = 7;
  return buf[1];
}

// Written and read at two different indices, which is where an unfocus that
// put the element back at the wrong place would show up.
uint32_t local_array_two()
  _ensures(return == 9)
{
  uint32_t buf[3];
  buf[0] = 2;
  buf[2] = 7;
  return buf[0] + buf[2];
}

uint32_t get_plain(_plain _array const uint32_t *a, size_t i, size_t n)
  _preserves(_inline_pulse(
    array_pts_to uint32_t_repr 4 (SizeT.v uint32_t_alignof) $(a) 0.5R $`values))
  _requires(i < n)
  _requires(_inline_pulse(pure (SizeT.v $(n) == Seq.length $`values)))
  _ensures(_inline_pulse(pure (SizeT.v $(i) < Seq.length $`values
    /\ $(return) == Seq.index $`values (SizeT.v $(i)))))
{
  return a[i];
}

struct pair {
  uint32_t x;
  uint32_t y;
};

uint32_t get_plain_field(_plain _array const struct pair *a, size_t i, size_t n)
  _preserves(_inline_pulse(
    array_pts_to struct_pair_repr 8 (SizeT.v struct_pair_alignof) $(a) 0.5R $`values))
  _requires(i < n)
  _requires(_inline_pulse(pure (SizeT.v $(n) == Seq.length $`values)))
  _ensures(_inline_pulse(pure (SizeT.v $(i) < Seq.length $`values
    /\ $(return) == (Seq.index $`values (SizeT.v $(i))).fld_x)))
{
  return a[i].x;
}
