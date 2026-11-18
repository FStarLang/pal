#include "pal.h"
#include <stdint.h>

struct store {
  int state;
  int count;
};

_plain struct store *get_store(_plain struct store *s0) _ensures(return == s0);

// `s` is a local the ghost statements move the contract's piece behind, so
// its fields are accessed in pieces, as the parameter's would be.
int bump(_plain struct store *s0)
  _ghost_arg(int c)
  _requires(_inline_pulse(int32_t_pts_to ($(s0) +! Struct_store.struct_store_offsetof_count) 1.0R $(c)))
  _requires(c < 100)
  _ensures(_inline_pulse(exists* (d: Int32.t). int32_t_pts_to ($(s0) +! Struct_store.struct_store_offsetof_count) 1.0R d))
  _ensures(return == c)
{
  struct store *s = get_store(s0);
  _ghost_stmt(rewrite each $(s0) as $(s));
  int n = s->count;
  s->count = n + 1;
  _ghost_stmt(rewrite each $(s) as $(s0));
  return n;
}

_include_pulse(Local_struct_pieces_include,
  module S = Struct_store

  let count_at (p: $type(struct store *)) : $type(struct store *) =
    p +! S.struct_store_offsetof_count

  let count_res (p: $type(struct store *)) : slprop =
    exists* (c: Int32.t). int32_t_pts_to (count_at p) 1.0R c

  // The whole store is not something this file treats in pieces...
  ghost fn count_of_whole (p: $type(struct store *)) (#v: erased S.struct_store)
    requires S.struct_store_pts_to p 1.0R v
    ensures S.struct_store_hole_count p 1.0R v ** count_res p
  {
    S.struct_store_focus_count p;
    fold (count_res p)
  }
)

// ...but this function's ghost code takes the counter by its field offset, so
// `s`, the local those statements name, is accessed field by field.
void bump_held(_plain struct store *s0)
  _preserves(_inline_pulse(Local_struct_pieces_include.count_res $(s0)))
{
  struct store *s = get_store(s0);
  _ghost_stmt(unfold (Local_struct_pieces_include.count_res $(s0)));
  _ghost_stmt(rewrite each (Local_struct_pieces_include.count_at $(s0))
    as ($(s) +! Struct_store.struct_store_offsetof_count));
  s->count = 0;
  _ghost_stmt(rewrite each ($(s) +! Struct_store.struct_store_offsetof_count)
    as (Local_struct_pieces_include.count_at $(s0)));
  _ghost_stmt(fold (Local_struct_pieces_include.count_res $(s0)));
}
