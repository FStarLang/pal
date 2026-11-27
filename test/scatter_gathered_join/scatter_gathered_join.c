#include "pal.h"
#include <stddef.h>

/* An object filled one field at a time through a snapshot local is whole
   again once its last field is written, and the join of an `if` with an
   `_ensures` that follows binds what it holds. The slot is named for the
   snapshot rather than for a variable, so the binder standing for its value
   must still be an identifier. (The `if`'s clause rebinds the box, so which
   object the cell is is not carried past it; the contract does not ask.) */

struct cell {
	unsigned int qlen;
	int lock;
};

struct box {
	struct cell *h;
	int tag;
};

int fill_all(_plain struct box *b, int c)
_requires(_inline_pulse(exists* (bv: struct_box).
	struct_box_pts_to $(b) 1.0R bv ** struct_cell_pts_to_uninit bv.fld_h))
_ensures(_inline_pulse(exists* (bv: struct_box) (p: ptr) (hv: struct_cell).
	struct_box_pts_to $(b) 1.0R bv ** struct_cell_pts_to p 1.0R hv))
{
	struct cell *h = NULL;
	int r = 0;
	h = b->h;
	_ghost_stmt(struct_cell_scatter_uninit $(h));
	_ghost_stmt($scattered(struct cell) $(h));
	h->qlen = 1;
	h->lock = 0;
	if (c)
		_ensures((_slprop)_inline_pulse(exists* (bv: struct_box).
			struct_box_pts_to $(b) 1.0R bv))
	{
		r = 1;
	} else {
		r = 2;
	}
	return r;
}
