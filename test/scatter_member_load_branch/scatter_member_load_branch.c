#include "pal.h"
#include <stddef.h>

/* The load is in one arm of a branch only: on the other path the local is
   still NULL, so no snapshot is taken. */

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
	if (c) {
		h = b->h;
	}
	_ghost_stmt(struct_head_scatter_uninit $(h));
	_ghost_stmt($scattered(struct head) $(h));
	h->list.next = 0;
	h->qlen = 1;
	_ghost_stmt(Fill_head.release $(h));
	_ghost_stmt($released(struct head) $(h));
	if (c) {
		r = 1;
	} else {
		r = 2;
	}
	return r;
}
