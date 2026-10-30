#include "pal.h"
#include <stddef.h>

struct _refine(_inline_pulse(pure (FStar.Int32.v $(this.x) > 0))) positive {
  int x;
};

int read_positive(const struct positive *p)
  _ensures(return > 0)
{
  return p->x;
}

void make_positive(_out struct positive *p) {
  p->x = 1;
}

struct _refine(this.x > 0 &&
               (_slprop)_inline_pulse(pure (FStar.Int32.v $(this.x) < 10))) bounded {
  int x;
};

int read_bounded(const struct bounded *p)
  _ensures(return > 0 && return < 10)
{
  return p->x;
}

_refine(this.x > 0)
typedef struct positive_pair {
  int x;
  int y;
} positive_pair;

struct positive_pair_box {
  positive_pair value;
};

int read_boxed_positive(const struct positive_pair_box *p)
  _ensures(return > 0)
{
  return p->value.x;
}

void make_boxed_positive(_out struct positive_pair_box *p) {
  p->value.x = 1;
  p->value.y = 2;
}

size_t refined_alignment(void)
  _ensures(return == _Alignof(int))
{
  return _Alignof(positive_pair);
}

_refine(this._length == 3)
typedef unsigned char byte_triplet[3];

size_t refined_array_alignment(void)
  _ensures(return == _Alignof(unsigned char))
{
  return _Alignof(byte_triplet);
}

// The refinement owns the cell as well as relating its contents to the record.
// The record's own storage is still granted by the ordinary pointer contract.
struct _refine(_inline_pulse(int32_t_pts_to $(this.cell) 1.0R $(this.x))) owned {
  int x;
  _plain int *cell;
};

int read_owned(const struct owned *p)
  _ensures(return == p->x)
{
  return *p->cell;
}

void update_owned(struct owned *p, int value) {
  p->x = value;
  *p->cell = value;
}

void make_owned(_out struct owned *p, _consumes int *cell) {
  p->x = *cell;
  p->cell = cell;
}

struct owned_box {
  struct owned value;
};

struct owned_outer {
  struct owned_box inner;
};

struct bounded_box {
  struct bounded value;
};

int read_nested_bounded(const struct bounded_box *p)
  _ensures(return > 0 && return < 10)
{
  return read_bounded(&p->value);
}

int read_nested_owned_value(struct owned_outer p)
  _ensures(return == p.inner.value.x)
{
  return *p.inner.value.cell;
}

int read_nested_owned(const struct owned_outer *p)
  _ensures(return == p->inner.value.x)
{
  return *p->inner.value.cell;
}

void update_nested_owned(struct owned_outer *p, int value) {
  p->inner.value.x = value;
  *p->inner.value.cell = value;
}

void make_nested_owned(_out struct owned_outer *p, _consumes int *cell) {
  p->inner.value.x = *cell;
  p->inner.value.cell = cell;
}

void keep_nested_nullable(_nullable const struct owned_outer *p) {}

void call_nested_null(void) {
  _ghost_stmt(intro_unless_null_null null
    (Struct_owned_outer.struct_owned_outer_pts_to null 1.0R
      { Struct_owned_outer.fld_inner =
        { Struct_owned_box.fld_value =
          { Struct_owned.fld_x = 0l; Struct_owned.fld_cell = null } } }));
  _ghost_stmt(intro_unless_null_null null (int32_t_pts_to null 1.0R 0l));
  keep_nested_nullable(NULL);
  _ghost_stmt(elim_unless_null_null null (int32_t_pts_to null 1.0R 0l));
  _ghost_stmt(elim_unless_null_null null
    (Struct_owned_outer.struct_owned_outer_pts_to null 1.0R
      { Struct_owned_outer.fld_inner =
        { Struct_owned_box.fld_value =
          { Struct_owned.fld_x = 0l; Struct_owned.fld_cell = null } } }));
}

void ignore_nested_plain(_plain struct owned_outer p) {}

struct plain_owned_box {
  _plain struct owned value;
};

void ignore_plain_field(struct plain_owned_box p) {}

void keep_nullable(_nullable const struct owned *p) {}

void call_null(void) {
  _ghost_stmt(intro_unless_null_null null
    (Struct_owned.struct_owned_pts_to null 1.0R
      { Struct_owned.fld_x = 0l; Struct_owned.fld_cell = null }));
  _ghost_stmt(intro_unless_null_null null (int32_t_pts_to null 1.0R 0l));
  keep_nullable(NULL);
  _ghost_stmt(elim_unless_null_null null (int32_t_pts_to null 1.0R 0l));
  _ghost_stmt(elim_unless_null_null null
    (Struct_owned.struct_owned_pts_to null 1.0R
      { Struct_owned.fld_x = 0l; Struct_owned.fld_cell = null }));
}
