#include "pal.h"
#include <stdint.h>

struct inner { uint32_t a; uint32_t b; };
struct outer { uint32_t tag; struct inner in; };

// Only the storage of `o->in` is held, and it holds no value yet: the
// assertion names that storage, so the whole-member store initialises it.
void init_inner(_plain struct outer *o)
  _requires(_inline_pulse(Struct_inner.struct_inner_pts_to_uninit ($(o) +! Struct_outer.struct_outer_offsetof_in)))
  _ensures(_inline_pulse(exists* v. Struct_inner.struct_inner_pts_to ($(o) +! Struct_outer.struct_outer_offsetof_in) 1.0R v **
    pure (v.fld_a == 1ul /\ v.fld_b == 2ul)))
{
  _assert(_inline_pulse(Struct_inner.struct_inner_pts_to_uninit $(&o->in)));
  o->in = (struct inner){ 1, 2 };
}
