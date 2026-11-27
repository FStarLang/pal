/* A mutable global this unit never writes, read with a fraction of its
 * points-to that the contract hands in rather than with `_live(g)`. */

#include "pal.h"
#include <stdint.h>

extern uint16_t mode;
extern uint32_t *table;

uint16_t read_mode(void)
    _requires(_inline_pulse(uint16_t_pts_to Global_mode.addr_var_mode 0.5R 7us))
    _ensures(_inline_pulse(uint16_t_pts_to Global_mode.addr_var_mode 0.5R 7us))
    _ensures(return == 7)
{
    return mode;
}

/* Any fraction will do, including one the caller knows nothing about. */
uint32_t *read_table(void)
    _requires(_inline_pulse(exists* (p: perm) (v: ptr).
        ptr_pts_to Global_table.addr_var_table p v))
    _ensures(_inline_pulse(exists* (p: perm) (v: ptr).
        ptr_pts_to Global_table.addr_var_table p v))
{
    return table;
}
