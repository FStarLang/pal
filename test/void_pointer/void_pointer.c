/* Failing test: conversions between `void *` and typed pointers.
 *
 * PAL emits `void *` as `ref unit`, but `unit` is a real inhabited type, so
 * `ref unit` is incompatible with every other pointer type. Clang records the
 * conversions in the IR, but the emitter's pointer-to-pointer cast arm emits
 * nothing for them, so PAL exits 0 with no diagnostic and the mismatch only
 * shows up as an F* error.
 *
 * A fix would emit `void *` as `Pulse.Lib.C.CoreRef.core_ref`, which already
 * has `ref_to_core` / `core_to_ref` casts and `core_null` / `core_is_null`.
 */

#include "pal.h"
#include <stdint.h>
#include <stddef.h>

struct counter {
  int32_t n;
};

/* Baseline: these verify today, and pin down where the boundary is. */

void take_void(void *p) { void *q = p; }

int32_t is_null(void *p) { return p == NULL; }

struct handle {
  void *raw;
  int32_t tag;
};

int32_t handle_tag(struct handle *h) { return h->tag; }

/* Failing: pass a typed pointer through an untyped interface and back.
 *
 *   * Error 189 at Func_roundtrip.fst: Ill-typed term
 *     - Expected expression of type Pulse.Lib.Reference.ref Prims.unit
 *       got expression __anf0 of type
 *          Pulse.Lib.Reference.ref Struct_counter.struct_counter
 */
void roundtrip(struct counter *c) {
  void *raw = (void *)c;
  struct counter *back = (struct counter *)raw;
  back->n = 0;
}

/* Failing the same way, but via the implicit `void *` conversion C allows.
 *
 *   * Error 189 at Func_implicit.fst: Ill-typed term
 *     - Expected expression of type
 *          Pulse.Lib.Reference.ref Struct_counter.struct_counter
 *       got expression __anf0 of type Pulse.Lib.Reference.ref Prims.unit
 */
void implicit(void *p) {
  struct counter *c = p;
  c->n = 0;
}
