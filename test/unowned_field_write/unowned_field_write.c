#include "pal.h"
#include <stddef.h>

// Writing a field the struct's `_own` does not read, through a pointer whose
// hand-written contract holds the struct but not its `_own`. Without
// `_unowned` the write is followed by `struct_gc_own_follow`, which needs the
// `_own` the function does not have.

struct node { int v; };

struct gc {
  struct node *dir; // owned: the struct's `_own` is `dir`'s points-to
  _plain void *pool;
};

// SNAP's Snap_Pointer_Move: take a pointer out of its slot, leaving NULL.
_plain void *move(void **p)
  _ensures(*p == NULL)
  _ensures(return == _old(*p));

void drop_pool(_plain void *pool);

// Holding the `_own`: it follows the struct to its new value.
void clear_owned(struct gc *g)
  _requires(_live(*g))
  _ensures(_live(*g) && g->pool == NULL)
{
  drop_pool(move((void **)&g->pool));
}

// A spliced contract holding the `_own` as well: still followed.
void clear_spliced(_plain struct gc *g)
  _requires(_inline_pulse(exists* (v: Struct_gc.struct_gc) (s: Struct_gc.struct_gc_own_spec).
              Struct_gc.struct_gc_pts_to $(g) 1.0R v ** Struct_gc.struct_gc_own v 1.0R s))
  _ensures(_inline_pulse(exists* (v: Struct_gc.struct_gc) (s: Struct_gc.struct_gc_own_spec).
              Struct_gc.struct_gc_pts_to $(g) 1.0R v ** Struct_gc.struct_gc_own v 1.0R s))
{
  g->pool = NULL;
}

// The points-to alone, `dir` lent elsewhere: a call writing the field ...
void clear_lent(_plain _unowned struct gc *g)
  _requires(_inline_pulse(exists* (v: Struct_gc.struct_gc). Struct_gc.struct_gc_pts_to $(g) 1.0R v))
  _ensures(_inline_pulse(exists* (v: Struct_gc.struct_gc). Struct_gc.struct_gc_pts_to $(g) 1.0R v))
{
  if (g->pool != NULL)
  {
    drop_pool(move((void **)&g->pool));
  }
}

// ... and a direct write, with the annotation on the prototype only.
void clear_lent_direct(_plain _unowned struct gc *g)
  _requires(_inline_pulse(exists* (v: Struct_gc.struct_gc). Struct_gc.struct_gc_pts_to $(g) 1.0R v))
  _ensures(_inline_pulse(exists* (v: Struct_gc.struct_gc).
             Struct_gc.struct_gc_pts_to $(g) 1.0R v ** pure (v.fld_pool == null)));

void clear_lent_direct(struct gc *g)
{
  g->pool = NULL;
}
