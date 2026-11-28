#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* The control for `scattered_if_write`: after the join, the field written in
   one arm is not taken to be storage again, so a second write into it needs
   the storage the context does not have. */

struct holder {
	void *slot;
	int32_t count;
};

void clear_twice(_plain struct holder *h)
_requires(_inline_pulse(Slot_pieces.pieces $(h)))
_ensures(_inline_pulse(Slot_pieces.pieces $(h)))
{
	_ghost_stmt(Slot_pieces.open_pieces $(h));
	_ghost_stmt($scattered(struct holder) $(h));
	if (h->slot != NULL)
		_ensures((_slprop)_inline_pulse(struct_holder_padding $(h) 1.0R **
			(exists* (p: ptr). ptr_pts_to ($(h) +! struct_holder_offsetof_slot) 1.0R p) **
			(exists* (c: FStar.Int32.t). int32_t_pts_to ($(h) +! struct_holder_offsetof_count) 1.0R c)))
	{
		_ghost_stmt(Slot_pieces.clear_slot $(h));
		h->slot = NULL;
	}
	h->slot = NULL;
	_ghost_stmt($released(struct holder) $(h));
	_ghost_stmt(Slot_pieces.close_pieces $(h));
}
