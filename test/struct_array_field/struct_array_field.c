#include "pal.h"

// Regression test for the struct array-field emission fix.
//
// Exercises `s->arr_field[i]` (read and write) on a struct passed by
// pointer.

typedef struct {
  _array unsigned *data;
} arr_struct;

void set_first(arr_struct *s, unsigned v)
  _requires(s->data._length >= 1)
  _preserves_value(s->data._length)
  _ensures(s->data[0] == v)
{
  s->data[0] = v;
}

unsigned get_first(arr_struct *s)
  _requires(s->data._length >= 1)
  _preserves_value(s->data._length)
  _ensures(return == s->data[0])
{
  return s->data[0];
}

void swap_first_two(arr_struct *s)
  _requires(s->data._length >= 2)
  _preserves_value(s->data._length)
{
  unsigned t = s->data[0];
  s->data[0] = s->data[1];
  s->data[1] = t;
}

void copy_first(arr_struct *src, arr_struct *dst)
  _requires(src->data._length >= 1)
  _requires(dst->data._length >= 1)
  _preserves_value(src->data._length)
  _preserves_value(dst->data._length)
{
  dst->data[0] = src->data[0];
}
