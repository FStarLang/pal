#include "pal.h"
#include <stdint.h>

/* The field is storage: reading it before the call that fills it fails. */

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

uint64_t fill_read_first(_plain struct report *r)
  _requires(_inline_pulse(Store.struct_report_hole_out $(r)))
  _requires(_inline_pulse(Struct_counts.struct_counts_pts_to_uninit $(&r->counts)))
  _ensures(_inline_pulse(Store.struct_report_hole_out $(r)))
  _ensures(_inline_pulse(exists* v. Struct_counts.struct_counts_pts_to $(&r->counts) 1.0R v))
{
  _assert(_inline_pulse(Store.struct_report_hole_out $(r)));
  _assert(_inline_pulse(Struct_counts.struct_counts_pts_to_uninit $(&r->counts)));
  uint64_t h = r->counts.hits;
  fill(&r->counts);
  return h;
}
