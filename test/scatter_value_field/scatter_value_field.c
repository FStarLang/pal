#include "pal.h"
#include <stddef.h>

/* A pointer field of a parameter passed by value names, through a
   `$scattered` hint, the object it points to: the object is tracked at the
   field's value, so naming a struct-typed field of it with its own hint, and
   writing through the field, cost no read of the parameter. */

struct lnk {
	struct lnk *next;
	struct lnk *prev;
};

struct head {
	struct lnk list;
	unsigned int qlen;
	int lock;
};

struct msg {
	struct head *h;
	int tag;
};

int fill_field(struct msg m, int c)
_requires(_inline_pulse(struct_head_pts_to_uninit $(m.h)))
_ensures(_inline_pulse(struct_head_pts_to_uninit $(m.h)))
{
	int r = 0;
	_ghost_stmt(struct_head_scatter_uninit $(m.h));
	_ghost_stmt($scattered(struct head) $(m.h));
	_ghost_stmt(struct_lnk_scatter_uninit $(&m.h->list));
	_ghost_stmt($scattered(struct lnk) $(&m.h->list));
	m.h->list.next = 0;
	m.h->qlen = 1;
	if (m.h->qlen == 1 && c) {
		r = 1;
	}
	_ghost_stmt(Fill_head.release $(m.h));
	_ghost_stmt($released(struct lnk) $(&m.h->list));
	_ghost_stmt($released(struct head) $(m.h));
	return r;
}
