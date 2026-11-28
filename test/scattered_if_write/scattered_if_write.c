#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* An object a contract hands over in pieces, with a field written in one
   arm of an `if` only. After the join the field is one the body has not
   written, read by address, and the `if`'s clause says what it holds. This
   is a handler clearing a slot on its store only if it was set.
   `scattered_if_write_bad` is the control: a later write still needs
   storage. */

struct holder {
	void *slot;
	int32_t count;
};

int32_t clear(_plain struct holder *h)
_requires(_inline_pulse(Slot_pieces.pieces $(h)))
_ensures(_inline_pulse(Slot_pieces.pieces $(h)))
{
	int32_t n;
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
	n = h->count;
	_ghost_stmt($released(struct holder) $(h));
	_ghost_stmt(Slot_pieces.close_pieces $(h));
	return n;
}
