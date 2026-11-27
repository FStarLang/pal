#include "pal.h"
#include <stddef.h>

/* A pointer local declared NULL and then loaded once from a field, with a
   `$scattered` hint after the load, is tracked at a snapshot of what it was
   loaded with: the writes fill the object by address. `$released` closes the
   fill when the author's own ghost step has taken the pieces back as
   storage, so the branch that follows carries nothing about the object. */

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
	h = b->h;
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

/* The same after an early exit: the `goto` puts the load and the hint
   together in the arm that falls through, which is where they are tracked. */
int fill_after_check(_plain struct box *b, int c)
_requires(_inline_pulse(exists* (bv: struct_box).
	struct_box_pts_to $(b) 1.0R bv ** struct_head_pts_to_uninit bv.fld_h))
_ensures(_inline_pulse(exists* (bv: struct_box).
	struct_box_pts_to $(b) 1.0R bv ** struct_head_pts_to_uninit bv.fld_h))
{
	struct head *h = NULL;
	int r = 0;
	if (c) {
		r = 3;
		goto done;
	}
	h = b->h;
	_ghost_stmt(struct_head_scatter_uninit $(h));
	_ghost_stmt($scattered(struct head) $(h));
	h->list.next = 0;
	h->qlen = 1;
	_ghost_stmt(Fill_head.release $(h));
	_ghost_stmt($released(struct head) $(h));
	r = 1;
done:
	return r;
}
