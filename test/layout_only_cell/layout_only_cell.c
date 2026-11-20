#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

/* Wider than the whole-record byte model, so the table has no array repr. */
struct wide_entry {
  int a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10;
  int b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10;
  int c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10;
};
struct counters { uint64_t count; };
struct layout_only {
  char prefix;
  int anchor;
  bool marked;
  struct counters counters;
  struct wide_entry entries[4];
};

uint64_t read_nested_counter(_plain int *anchor)
  _ghost_arg(uint64_t n)
  _preserves(_inline_pulse(uint64_t_pts_to
    (($(anchor) -? Struct_layout_only.struct_layout_only_offsetof_anchor)
      +! Struct_layout_only.struct_layout_only_offsetof_counters
      +! Struct_counters.struct_counters_offsetof_count) 0.5R $(n)))
  _ensures(return == n)
{
  struct layout_only *p = _container_of(anchor, struct layout_only, anchor);
  return p->counters.count;
}

#define FLAG_AT(anchor) \
  (($(anchor) -? Struct_layout_only.struct_layout_only_offsetof_anchor) \
    +! Struct_layout_only.struct_layout_only_offsetof_marked)

bool mark_from_anchor(_plain int *anchor)
  _ghost_arg(bool old)
  _requires(_inline_pulse(bool_t_pts_to FLAG_AT(anchor) 1.0R $(old)))
  _ensures(_inline_pulse(bool_t_pts_to FLAG_AT(anchor) 1.0R $((_Bool)1)))
  _ensures(return == old)
{
  struct layout_only *p = _container_of(anchor, struct layout_only, anchor);
  bool was_marked = p->marked;
  p->marked = true;
  return was_marked;
}

void mark_with_read_share(_plain int *anchor)
  _preserves(_inline_pulse(bool_t_pts_to FLAG_AT(anchor) 0.5R $((_Bool)0)))
{
  struct layout_only *p = _container_of(anchor, struct layout_only, anchor);
  p->marked = true;
}
