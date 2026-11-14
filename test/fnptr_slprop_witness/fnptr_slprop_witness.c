#include "pal.h"
#include <stdint.h>

/* A function whose address is taken and which carries a `_ghost_arg` of type
   `_slprop`: the frame its caller keeps across the call. The wrapper's witness
   is then an `erased slprop`, which lives in a higher universe than the data a
   function pointer's arguments are, so the function-pointer library has to
   take a witness type of any universe. */

typedef void (*cb_t)(int32_t *q);

struct cfg {
	cb_t cb;
	cb_t plain;
};

_ghost_arg(_slprop F)
_requires(_inline_pulse(Pulse.Lib.C.Palow.CTypes.int32_t_pts_to $(q) 1.0R 0l ** $(F)))
_ensures(_inline_pulse(Pulse.Lib.C.Palow.CTypes.int32_t_pts_to $(q) 1.0R 1l ** $(F)))
void set_one(_plain int32_t *q) { *q = 1; }

/* Its plain counterpart: no ghost argument, so a `Type0` witness. */
_requires(_inline_pulse(Pulse.Lib.C.Palow.CTypes.int32_t_pts_to $(q) 1.0R 0l))
_ensures(_inline_pulse(Pulse.Lib.C.Palow.CTypes.int32_t_pts_to $(q) 1.0R 0l))
void keep_zero(_plain int32_t *q) { (void)q; }

void take(struct cfg *c) { c->cb = set_one; }

/* Called through the pointer: the frame `F` is the caller's `r`. */
_ghost_arg(_slprop F)
_requires(_inline_pulse(Pulse.Lib.C.Palow.CTypes.int32_t_pts_to $(q) 1.0R 0l ** $(F)))
_ensures(_inline_pulse(Pulse.Lib.C.Palow.CTypes.int32_t_pts_to $(q) 1.0R 1l ** $(F)))
void call_it(_plain int32_t *q)
{
	cb_t f = set_one;
	f(q);
}

/* Handing a local configuration that holds the pointer to a callee: the
   validity is then put down by inference, at an address the emitter no longer
   spells, and its witness type has to be pinned for the universe to resolve. */
void use_cfg(struct cfg *c);

void install(void)
{
	struct cfg c;
	c.cb = set_one;
	c.plain = keep_zero;
	use_cfg(&c);
}
