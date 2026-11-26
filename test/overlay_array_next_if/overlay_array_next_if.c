#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

typedef union word {
    struct { int32_t lo; uint32_t hi; };
    uint64_t bits;
} word;

struct entry { uint32_t count; word saved; };
union _overlay view { struct entry entry; uint64_t prefix; };
struct group { uint32_t tag; struct entry entries[8]; };

bool wide(void);

// The conditional operator makes the store of the whole initializer a
// conditional, so each arm writes all eight fresh elements. The hint states
// what both arms establish, which is all the join has to carry.
void fresh_group(_plain struct group *p)
  _requires(_inline_pulse(struct_group_pts_to_uninit $(p)))
  _ensures(_inline_pulse(exists* g. struct_group_pts_to $(p) 1.0R g **
      pure ((g.fld_tag == 1ul \/ g.fld_tag == 2ul)
            /\ (FStar.Seq.index g.fld_entries 7).fld_count == 5ul)))
{
    _ghost_stmt(pal_next_if requires struct_group_pts_to_uninit $(p)
        ensures exists* g. struct_group_pts_to $(p) 1.0R g **
            pure (g.fld_tag == 1ul \/ g.fld_tag == 2ul));
    _ghost_stmt($unfold-uninit(struct group) $(p));
    *p = (struct group){ .tag = wide() ? 1 : 2 };
    p->entries[7].count = 5;
}
