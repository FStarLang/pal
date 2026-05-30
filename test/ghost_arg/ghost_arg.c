#include "pal.h"

_type(tank, cap: nat & Pulse.Lib.Tank.tank cap)
_let(_specint tank_cap(tank t), _inline_pulse($(t)._1))

_let(_slprop tank_owns(tank t, _specnat amt),
    _inline_pulse(Pulse.Lib.Tank.owns $(t)._2 $(amt)))

int foo()
    _ghost_arg(tank t) // becomes an extra argument (#var_t: erased tank)
    _preserves(tank_owns(t, 1))
{
    return 67;
}