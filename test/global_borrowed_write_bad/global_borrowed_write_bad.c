/* A fraction of a mutable global's points-to lets a body read it, never
 * write it. A function that writes the global owns it in full, so it does
 * not meet a callback specification that brings only a fraction. */

#include "pal.h"
#include <stdint.h>

extern uint16_t mode;

typedef uint16_t (*hook)(void);

/* The callback specification: a fraction of `mode`, and nothing else. */
uint16_t peek(void)
    _requires(_inline_pulse(exists* (p: perm) (v: FStar.UInt16.t).
        uint16_t_pts_to Global_mode.addr_var_mode p v ** pure (p <. 1.0R)))
    _ensures(_inline_pulse(exists* (p: perm) (v: FStar.UInt16.t).
        uint16_t_pts_to Global_mode.addr_var_mode p v ** pure (p <. 1.0R)))
{
    return mode;
}

/* A writer, defined in another unit: it needs all of `mode`. */
uint16_t poke(void)
    _requires(_inline_pulse(exists* (v: FStar.UInt16.t).
        uint16_t_pts_to Global_mode.addr_var_mode 1.0R v))
    _ensures(_inline_pulse(exists* (v: FStar.UInt16.t).
        uint16_t_pts_to Global_mode.addr_var_mode 1.0R v));

void install(hook h
                 _refine((_slprop) _inline_pulse(
                     is_valid $(this) true
                         (pre_of Funcptr_peek.func_peek__fp)
                         (post_of Funcptr_peek.func_peek__fp))))
{
}

/* Control: the reader meets the specification. */
void install_peek(void)
{
    install(peek);
}

/* The writer does not. */
void install_poke(void)
{
    install(poke);
}
