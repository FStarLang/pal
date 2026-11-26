#include "pal.h"
#include <stdint.h>

struct inner { uint32_t a; uint32_t b; };
struct outer { uint32_t tag; struct inner in; };

// `o->in` already holds a value, so the assertion that its storage is
// uninitialised -- the only thing that selects an initialising store -- fails.
void init_inner(_plain struct outer *o)
  _requires(_inline_pulse(exists* v. Struct_inner.struct_inner_pts_to ($(o) +! Struct_outer.struct_outer_offsetof_in) 1.0R v))
  _ensures(_inline_pulse(exists* v. Struct_inner.struct_inner_pts_to ($(o) +! Struct_outer.struct_outer_offsetof_in) 1.0R v))
{
  _assert(_inline_pulse(Struct_inner.struct_inner_pts_to_uninit $(&o->in)));
  o->in = (struct inner){ 1, 2 };
}
