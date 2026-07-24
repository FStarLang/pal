#include "pal.h"

// Regression test for the merge pass dropping a declaration's ghost arguments.
//
// The forward declaration carries a `_ghost_arg` plus a spec that mentions it,
// while the definition omits the ghost arg (a common split: contract on the
// prototype, plain body below). The merge pass copies the declaration's
// requires/ensures into the spec-less definition; it must ALSO reintroduce the
// declaration's ghost args, otherwise the emitted `fn` signature has no binder
// for `var_t` even though the copied spec (and, in general, the body) reference
// it -- yielding F* "Error 72: Identifier not found: var_t".

_type(tank, cap: nat & Pulse.Lib.Tank.tank cap)

_let(_slprop tank_owns(tank t, _specnat amt),
    _inline_pulse(Pulse.Lib.Tank.owns $(t)._2 $(amt)))

// Declaration: ghost arg + spec referencing it.
int ghost_decl_only()
    _ghost_arg(tank t)
    _preserves(tank_owns(t, 1));

// Definition: no `_ghost_arg`. The merged function must still take
// `(#var_t: erased tank)` so the inherited `_preserves(tank_owns(t, 1))`
// resolves.
int ghost_decl_only()
{
    return 67;
}
