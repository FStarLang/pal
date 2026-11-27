#include "pal.h"
#include <stddef.h>

/* A load and its `$scattered` hint inside a loop body are not tracked at a
   snapshot: the body runs the load again on every iteration. The writes
   focus the whole object, which is storage, and are rejected. */

struct lnk {
	struct lnk *next;
	struct lnk *prev;
};

struct head {
	struct lnk list;
	unsigned int qlen;
	int lock;
};

struct box {
	struct head *h;
	int tag;
};

int fill_some(_plain struct box *b, int c)
_requires(_inline_pulse(exists* (bv: struct_box).
	struct_box_pts_to $(b) 1.0R bv ** struct_head_pts_to_uninit bv.fld_h))
_ensures(_inline_pulse(exists* (bv: struct_box).
	struct_box_pts_to $(b) 1.0R bv ** struct_head_pts_to_uninit bv.fld_h))
{
	struct head *h = NULL;
	int r = 0;
	while (c)
		_invariant(_live(c) && _live(r) && _live(h))
	{
		h = b->h;
		_ghost_stmt(struct_head_scatter_uninit $(h));
		_ghost_stmt($scattered(struct head) $(h));
		h->list.next = 0;
		h->qlen = 1;
		_ghost_stmt(Fill_head.release $(h));
		_ghost_stmt($released(struct head) $(h));		c = 0;
	}
	return r;
}
