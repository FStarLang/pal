#include "pal.h"
#include <stddef.h>

// A pointer field's address handed to a call through a cast to another
// pointer-to-pointer type, as SNAP's Snap_Pointer_Move does with
// `(void **)(&p->f)`. The field is lent for the call the same as uncast.

struct node { int v; };
typedef struct pool *PPOOL;

struct gc {
  struct node *dir;
  _plain PPOOL pool;
};

_plain void *move(void **p)
  _ensures(*p == NULL)
  _ensures(return == _old(*p));

#define MOVE(P) \
  _Generic(*(P), void *: move((void **)(P)), \
           default: (__typeof__(*(P)))move((void **)(P)))

void drop_pool(_plain PPOOL pool);

void drop_node(_plain struct node *n);

void clear_pool(struct gc *g)
  _requires(_live(*g))
  _ensures(_live(*g) && g->pool == NULL)
{
  drop_pool(MOVE(&g->pool));
}

void clear_pool_local(struct gc *g)
  _requires(_live(*g))
  _ensures(_live(*g) && g->pool == NULL)
{
  PPOOL p = (PPOOL)move((void **)&g->pool);
  drop_pool(p);
}

// The owned field, with the struct's `_own` held elsewhere.
void clear_dir(_plain _unowned struct gc *g)
  _requires(_inline_pulse(exists* (v: Struct_gc.struct_gc). Struct_gc.struct_gc_pts_to $(g) 1.0R v))
  _ensures(_inline_pulse(exists* (v: Struct_gc.struct_gc).
              Struct_gc.struct_gc_pts_to $(g) 1.0R v ** pure (v.fld_dir == null)))
{
  drop_node(MOVE(&g->dir));
}
