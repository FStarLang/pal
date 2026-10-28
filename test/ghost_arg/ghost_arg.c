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

int bar()
    _ghost_arg(unsigned n)
    _ghost_arg(tank t)
    _preserves(tank_owns(t, n))
{
    return 42;
}

void frame()
    _ghost_arg(_slprop P)
    _preserves(_inline_pulse($(P)))
{
}

_pure int identity(int n)
    _ensures(_inline_pulse($(return) == $(n)))
{
    return n;
}

int identity_client(int n) _ensures(return == identity(n))
{
    return n;
}