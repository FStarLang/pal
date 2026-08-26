#include "pal.h"
#include <stdint.h>

// Minimal repro: a `_refine`d struct parameter makes a function pointer
// unusable in an ops table. `struct a`/`on_a`/`fa` is the control; `struct b`/
// `on_b`/`fb` is the case under test. The two halves are identical apart from
// the single `_refine` on `b`, so any difference in the emitted wrappers is
// attributable to the refinement alone.
//
// The attribute has to be written *after* the `struct` keyword; writing it
// before makes clang drop the annotation (see test/refine_struct).

struct a { int32_t x; };                      // control: no _refine
struct _refine(this.x == 1) b { int32_t x; }; // same, plus one refinement

static int32_t on_a(struct a *p) { return p->x; }
static int32_t on_b(struct b *p) { return p->x; }

struct ops {
  int32_t (*fa)(struct a *);
  int32_t (*fb)(struct b *);
};

const struct ops the_ops = {.fa = on_a, .fb = on_b};

// Indirect call through the refined callback. The decay above only exercises
// `of_fn_div`; this exercises `call_div`, where the caller must *match* the
// wrapper's precondition -- refinement `with_pure` included -- against
// `pre_of`. That is where wrapping the requires in an identity could plausibly
// disturb slprop matching, so it is worth covering explicitly.
int32_t apply_b(int32_t (*op)(struct b *)
                    _refine((_slprop) _inline_pulse(
                        Pulse.Lib.C.FuncPtr.is_valid $(this) true
                            (Pulse.Lib.C.FuncPtr.pre_of Funcptr_on_b.func_on_b__fp) (Pulse.Lib.C.FuncPtr.post_of Funcptr_on_b.func_on_b__fp))),
                struct b *p)
{
  return op(p);
}
