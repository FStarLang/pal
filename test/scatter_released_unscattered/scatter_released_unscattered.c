#include "pal.h"
#include <stddef.h>

/* `$released` of an object that was never `$scattered` or written: the
   emitter refuses it. */

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
	_ghost_stmt($released(struct head) $(h));
	if (c) {
		r = 1;
	} else {
		r = 2;
	}
	return r;
}
