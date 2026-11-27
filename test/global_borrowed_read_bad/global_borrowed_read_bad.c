/* A read of a mutable global still needs a points-to for it. */

#include "pal.h"
#include <stdint.h>

extern uint16_t mode;

uint16_t read_mode_unowned(void)
{
    return mode;
}
