#include "pal.h"

/* The local is retargeted through its address after the scatter. The writes
   that follow go through the new pointer, not into the scattered storage, so
   the pieces are never filled and the object cannot be gathered. */

struct head {
	unsigned int qlen;
	int lock;
	unsigned int tail;
};

void retarget(_plain struct head **slot, _plain struct head *other)
_requires(_inline_pulse(exists* (h: ptr).
	ptr_pts_to $(slot) 1.0R h **
	struct_head_padding h 1.0R **
	uint32_t_pts_to_uninit (h +! struct_head_offsetof_qlen) **
	uint32_t_pts_to_uninit (h +! struct_head_offsetof_tail) **
	(exists* (l: Int32.t). int32_t_pts_to (h +! struct_head_offsetof_lock) 1.0R l)))
_ensures(_inline_pulse(exists* (h: ptr) v.
	ptr_pts_to $(slot) 1.0R h ** struct_head_pts_to h 1.0R v))
{
	struct head *h = *slot;
	_ghost_stmt($scattered(struct head) $(h));
	struct head **hp = &h;
	*hp = other;
	h->qlen = 1;
	h->tail = 2;
	_ghost_stmt(struct_head_gather $(h));
}
