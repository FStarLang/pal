#include "pal.h"

/* The cast local is pointed elsewhere after its `$scattered` hint. The write
   that follows goes to the new object, not into the tracked storage, so it
   must not be taken as a write of the tracked field. */

struct head {
	unsigned int qlen;
	int lock;
};

void retarget_cast(_plain void *e, _plain void *other)
_requires(_inline_pulse(struct_head_pts_to_uninit $(e)))
_ensures(_inline_pulse(exists* v. struct_head_pts_to $(e) 1.0R v))
{
	struct head *h = (struct head *)e;
	_ghost_stmt(struct_head_scatter_uninit $(h));
	_ghost_stmt($scattered(struct head) $(h));
	h = (struct head *)other;
	h->qlen = 1;
	h->lock = 2;
	_ghost_stmt($released(struct head) $(h));
	_ghost_stmt(struct_head_gather $(e));
}
