#include "pal.h"
#include <stdint.h>

/* An `_out` argument that is a field of an object held in pieces, into
   storage: an `_assert` of the field's `_pts_to_uninit` says there is no
   value there, so the field goes to the callee as it is, with no `_forget`
   first -- there is nothing to forget, and asking for a value would fail. */

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

/* The rest of `*r` on a user loan (Store.struct_report_hole_out), the
   field as storage beside it. */
void fill_user_hole(_plain struct report *r)
  _requires(_inline_pulse(Store.struct_report_hole_out $(r)))
  _requires(_inline_pulse(Struct_counts.struct_counts_pts_to_uninit $(&r->counts)))
  _ensures(_inline_pulse(Store.struct_report_hole_out $(r)))
  _ensures(_inline_pulse(exists* v. Struct_counts.struct_counts_pts_to $(&r->counts) 1.0R v))
{
  _assert(_inline_pulse(Store.struct_report_hole_out $(r)));
  _assert(_inline_pulse(Struct_counts.struct_counts_pts_to_uninit $(&r->counts)));
  fill(&r->counts);
}

/* The same with the generated hole, whose `kind` holds a value. */
void fill_generated_hole(_plain struct report *r)
  _ghost_arg(struct report saved)
  _requires(_inline_pulse(Struct_report.struct_report_hole_counts $(r) 1.0R $(saved)))
  _requires(_inline_pulse(Struct_counts.struct_counts_pts_to_uninit $(&r->counts)))
  _ensures(_inline_pulse(exists* v. Struct_report.struct_report_pts_to $(r) 1.0R v))
{
  _assert(_inline_pulse(Struct_report.struct_report_hole_counts $(r) 1.0R $(saved)));
  _assert(_inline_pulse(Struct_counts.struct_counts_pts_to_uninit $(&r->counts)));
  fill(&r->counts);
  _ghost_stmt(Struct_report.struct_report_unfocus_counts $(r));
}
