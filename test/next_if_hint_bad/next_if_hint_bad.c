#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

bool flag(void);

// No conditional follows the hint.
uint32_t unused(uint32_t x)
  _ensures(return == x)
{
    _ghost_stmt(pal_next_if requires emp ensures emp);
    return x;
}

// A hint needs both a requires and an ensures.
uint32_t no_requires(void)
  _ensures(return == 1 || return == 2)
{
    _ghost_stmt(pal_next_if ensures emp);
    return flag() ? 1 : 2;
}

// Only one hint may wait for the next conditional.
uint32_t twice(void)
  _ensures(return == 1 || return == 2)
{
    _ghost_stmt(pal_next_if requires emp ensures emp);
    _ghost_stmt(pal_next_if requires emp ensures emp);
    return flag() ? 1 : 2;
}

// A conditional with its own `_ensures` cannot take a hint as well.
void competing(uint32_t *p)
  _ensures(*p == 1 || *p == 2)
{
    _ghost_stmt(pal_next_if requires emp ensures emp);
    if (flag())
        _ensures(*p == 1 || *p == 2)
    {
        *p = 1;
    } else {
        *p = 2;
    }
}
