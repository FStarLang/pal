#include "pal.h"
#include <stdint.h>

/* Without storage for the field the assertion that would make the call pass
   it as uninit has nothing to prove it from, and fails. */

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

void fill_no_storage(_plain struct report *r)
  _requires(_inline_pulse(Store.struct_report_hole_out $(r)))
  _ensures(_inline_pulse(Store.struct_report_hole_out $(r)))
{
  _assert(_inline_pulse(Store.struct_report_hole_out $(r)));
  _assert(_inline_pulse(Struct_counts.struct_counts_pts_to_uninit $(&r->counts)));
  fill(&r->counts);
}
