#include "pal.h"

/* `_pulse_opaque_to_smt` on an immutable struct global keeps the value from
   the solver, so that a table of function pointers does not put every
   callee's contract in front of it in every module that can see the table.
   A specification that names a field therefore holds only after a proof has
   revealed the value, and one that names it without revealing it must be
   rejected -- otherwise nothing would notice the attribute being dropped. */

struct ops {
  int k;
};

static const _pulse_opaque_to_smt struct ops opaque_ops = {.k = 4};

void peek_k(void)
    _ensures(_inline_pulse(pure (Global_opaque_ops.var_opaque_ops.Struct_ops.fld_k == 4l)))
{
}
