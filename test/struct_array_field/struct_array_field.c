#include "pal.h"

// Regression test for the struct array-field emission fix.
//
// Exercises `s->arr_field[i]` (read and write) on a struct passed by
// pointer. Before the fix, Member access on an _array T * field went
// through __get_<fld>, which returned an awkward `ref (array T)`
// requiring a `!` deref at the call site (only verifying through a
// chain of rewrites_to that happened to bottom out at the value-record
// path). After the fix, Member access for an array field on an LValue
// receiver emits `(!x).struct_S__f` directly, so the handle the user
// works with is exactly the path the struct predicate speaks about.

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
