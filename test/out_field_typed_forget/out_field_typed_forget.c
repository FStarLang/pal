#include "pal.h"
#include <stdint.h>

/* An `_out` field of an object held in pieces whose field holds a value,
   with no assertion that it is storage: the value is forgotten before the
   call, as before. Without the `_forget` the call would find no storage. */

struct counts {
  uint64_t hits;
  uint64_t misses;
};

struct report {
  uint32_t kind;
  struct counts counts;
};

void fill(_out struct counts *dst)
  _ensures(dst->hits == 1 && dst->misses == 2)
{
  dst->hits = 1;
  dst->misses = 2;
}

void fill_typed(_plain struct report *r)
  _ghost_arg(struct report saved)
  _requires(_inline_pulse(Struct_report.struct_report_hole_counts $(r) 1.0R $(saved)))
  _requires(_inline_pulse(exists* v. Struct_counts.struct_counts_pts_to $(&r->counts) 1.0R v))
  _ensures(_inline_pulse(exists* v. Struct_report.struct_report_pts_to $(r) 1.0R v))
{
  _assert(_inline_pulse(Struct_report.struct_report_hole_counts $(r) 1.0R $(saved)));
  fill(&r->counts);
  _ghost_stmt(Struct_report.struct_report_unfocus_counts $(r));
}
