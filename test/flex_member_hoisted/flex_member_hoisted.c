#include "pal.h"
#include <stdint.h>

// The container is declared before its element type is defined, so merging
// hoists its definition up to that declaration. Its flexible array member
// still needs the element's layout first.
typedef struct _container *PCONTAINER;

typedef struct _slab {
  uint32_t state;
  struct _slab *next;
} SLAB;

typedef struct _container {
  uint64_t cb;
  uint32_t count;
  uint32_t active;
  SLAB slabs[];
} CONTAINER;

uint32_t container_count(_plain PCONTAINER c)
  _ghost_arg(uint32_t n)
  _preserves(_inline_pulse(uint32_t_pts_to
    ($(c) +! Struct__container.struct__container_offsetof_count) 1.0R $(n)))
  _ensures(return == n)
{
  return c->count;
}

uint32_t *slab_state(_plain PCONTAINER c, uint32_t i)
  _ensures(_inline_pulse(pure ($(return) ==
    (($(c) +! Struct__container.struct__container_offsetof_slabs)
      +! (Struct__slab.struct__slab_sizeof `SizeT.mul` SizeT.uint32_to_sizet $(i)))
      +! Struct__slab.struct__slab_offsetof_state)))
{
  return &c->slabs[i].state;
}
