#include "pal.h"

// Regression test for the arrayptr comparison specs
// (arrayptr_lt / arrayptr_lte / arrayptr_eq). Their `ensures` must tie the
// boolean result to the actual offset comparison; an earlier version asserted
// the ordering unconditionally, which was unsound (and, dually, also rejected
// this correct program because the false branch could not be discharged).
//
// p = a + 2, q = a + 5, so p < q holds and this returns 1 in real C.
int less(_array int *a)
  _requires(a._length == 10)
  _ensures(return == 1)
{
  _arrayptr int *p = a + 2;
  _arrayptr int *q = a + 5;
  if (p < q) { return 1; } else { return 0; }
}
