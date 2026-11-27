#include "pal.h"

/* A pointer local loaded once from memory names the same storage at every
   use, as one returned by a call does: storage `$scattered` says is in pieces
   is filled field by field through it. */

struct head {
	unsigned int qlen;
	int lock;
	unsigned int tail;
};

void fill_loaded(_plain struct head **slot)
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
	h->qlen = 1;
	h->tail = 2;
	_ghost_stmt(struct_head_gather $(h));
}
