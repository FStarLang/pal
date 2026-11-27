#include "pal.h"
#include <stddef.h>

/* The load and its `$scattered` hint sit together in the first arm, so a
   snapshot could cover that arm only. The second arm uses the local again
   after the block that holds the load: no snapshot reaches it, so none is
   taken for either, and the writes focus the whole object, which is
   storage. */

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
		_ghost_stmt(struct_head_scatter_uninit $(h));
		_ghost_stmt($scattered(struct head) $(h));
		h->list.next = 0;
		h->qlen = 1;
		_ghost_stmt(Fill_head.release $(h));
		_ghost_stmt($released(struct head) $(h));
		r = 1;
	}
	if (c) {
		_ghost_stmt(struct_head_scatter_uninit $(h));
		_ghost_stmt($scattered(struct head) $(h));
		h->list.next = 0;
		h->qlen = 1;
		_ghost_stmt(Fill_head.release $(h));
		_ghost_stmt($released(struct head) $(h));
	}
	return r;
}
