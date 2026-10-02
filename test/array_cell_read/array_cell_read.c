/* Test: returning an array cell that was borrowed only to read.
 *
 * `T *p = &a[i];` borrows cell `i` (`array_borrow_cell`), and the borrow must
 * be given back before the array is used whole again. `array_return_cell`
 * puts the cell back as `array_spec_set s i v`, which is not syntactically
 * `s`. `array_return_cell_unchanged` is the read-only return: the array
 * comes back as exactly the `s` it was borrowed from.
 *
 * In the shapes below Z3 can also close the gap after `array_return_cell`,
 * so this test pins the API's use from C rather than its necessity. The
 * exact spec matters where the array's spec is matched syntactically, e.g.
 * under a value-keyed predicate of an enclosing object; the ghost function
 * itself is proved in Pulse.Lib.C.Array.
 */

#include "pal.h"
#include <stdint.h>
#include <stddef.h>

#define N 4

struct ctx {
  uint64_t id;
  uint64_t flags;
};

uint64_t id_at(_array struct ctx *all, size_t idx) _requires(all._length == N)
    _requires(idx < N) _ensures(all._length == N)
    _ensures(return == all[idx].id)
    _ensures(_forall(size_t k, k < N ==> all[k].id == _old(all[k].id))) {
  struct ctx *c = &all[idx];
  uint64_t r = c->id;
#ifndef PALOW
  /* Palow gives the cell back with `array_unfocus_read`, which the emitter
     already writes; only the old model needs the step spelled out. */
  _ghost_stmt(Pulse.Lib.C.Array.array_return_cell_unchanged (!var_all));
#endif
  return r;
}

/* Two reads in a row: the second call needs the array back whole. */
uint64_t id_pair(_array struct ctx *all) _requires(all._length == N)
    _ensures(all._length == N) {
  uint64_t a = id_at(all, 0);
  uint64_t b = id_at(all, 3);
  return a ^ b;
}
