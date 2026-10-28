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
