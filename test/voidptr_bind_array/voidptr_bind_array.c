#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// Binding a caller-supplied `void *` buffer to an array-typed slot: the
// implicit `void * -> T *` conversion lands on an `_array`/`_arrayptr` lvalue.
// The coercion is a view of the raw address; it carries no ownership, so a
// reader still needs the array's points-to from somewhere else.

typedef struct _rec {
    uint32_t a;
    uint64_t b;
} rec;

typedef struct _table {
    uint32_t version;
    uint32_t count;
    union {
        _array rec *v1;
    } entries;
} table;

typedef struct _cursor {
    _arrayptr rec *cur;
} cursor;

_include_pulse(VoidptrBindArray,
  let recs_of (p: Pulse.Lib.C.CoreRef.core_ref) : array Typedef_rec.ty_rec =
    Pulse.Lib.C.Array.ref_to_array
      (Pulse.Lib.C.CoreRef.core_to_ref Typedef_rec.ty_rec p)

  // The coercion alone grants nothing: reading through it without the
  // array's points-to must fail.
  [@@expect_failure]
  fn read_without_ownership (p: Pulse.Lib.C.CoreRef.core_ref)
    returns r: Typedef_rec.ty_rec
  {
    array_read (recs_of p) 0sz
  }
)

void bind_union_member(table *t, void *buf)
{
    t->version = 1;
    t->entries.v1 = buf;
}

void bind_arrayptr_field(cursor *c, void *buf)
{
    c->cur = buf;
}

uint32_t read_first(void *buf)
  _preserves(_inline_pulse(
    exists* (s: full_array_spec Typedef_rec.ty_rec).
      array_pts_to (VoidptrBindArray.recs_of $(buf)) 1.0R s **
      pure (array_spec_len s == 1) **
      pure (array_spec_initd s 0)))
{
    _array rec *recs = buf;
    return recs[0].a;
}
