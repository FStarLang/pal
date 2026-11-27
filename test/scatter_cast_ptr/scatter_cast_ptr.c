#include "pal.h"
#include <stddef.h>

/* A pointer local initialised once with a parameter's value under a cast,
   with a `$scattered` hint after it, is tracked at a snapshot of that value
   the way a loaded one is: the writes fill the object by address. */

struct lnk {
	struct lnk *next;
	struct lnk *prev;
};

struct head {
	struct lnk list;
	unsigned int qlen;
	int lock;
};

int fill_cast(_plain void *e, int c)
_requires(_inline_pulse(struct_head_pts_to_uninit $(e)))
_ensures(_inline_pulse(struct_head_pts_to_uninit $(e)))
{
	struct head *h = (struct head *)e;
	int r = 0;
	_ghost_stmt(struct_head_scatter_uninit $(h));
	_ghost_stmt($scattered(struct head) $(h));
	h->list.next = 0;
	h->qlen = 1;
	_ghost_stmt(Fill_head.release $(h));
	_ghost_stmt($released(struct head) $(h));
	if (c) {
		r = 1;
	}
	return r;
}

/* A struct-typed field of that object named by its own `$scattered` hint is
   tracked off the same snapshot, so naming it costs no read of the local. */
int fill_cast_nested(_plain void *e, int c)
_requires(_inline_pulse(struct_head_pts_to_uninit $(e)))
_ensures(_inline_pulse(struct_head_pts_to_uninit $(e)))
{
	struct head *h = (struct head *)e;
	int r = 0;
	_ghost_stmt(struct_head_scatter_uninit $(h));
	_ghost_stmt($scattered(struct head) $(h));
	_ghost_stmt(struct_lnk_scatter_uninit $(&h->list));
	_ghost_stmt($scattered(struct lnk) $(&h->list));
	h->list.next = 0;
	h->qlen = 1;
	_ghost_stmt(Fill_head.release $(h));
	_ghost_stmt($released(struct lnk) $(&h->list));
	_ghost_stmt($released(struct head) $(h));
	if (c) {
		r = 1;
	}
	return r;
}
