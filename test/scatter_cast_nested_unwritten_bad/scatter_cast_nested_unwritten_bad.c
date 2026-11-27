#include "pal.h"

/* A nested `$released` ends the tracking of a field; it does not fill it. One
   of the field's own fields is never written, so the field cannot be gathered
   as initialised. */

struct lnk {
	struct lnk *next;
	struct lnk *prev;
};

struct head {
	struct lnk list;
	unsigned int qlen;
	int lock;
};

void fill_partial(_plain void *e)
_requires(_inline_pulse(struct_head_pts_to_uninit $(e)))
_ensures(_inline_pulse(exists* v. struct_lnk_pts_to ($(e) +! struct_head_offsetof_list) 1.0R v **
	uint32_t_pts_to_uninit ($(e) +! struct_head_offsetof_qlen) **
	int32_t_pts_to_uninit ($(e) +! struct_head_offsetof_lock) **
	struct_head_padding $(e) 1.0R))
{
	struct head *h = (struct head *)e;
	_ghost_stmt(struct_head_scatter_uninit $(h));
	_ghost_stmt($scattered(struct head) $(h));
	_ghost_stmt(struct_lnk_scatter_uninit $(&h->list));
	_ghost_stmt($scattered(struct lnk) $(&h->list));
	h->list.next = 0;
	_ghost_stmt($released(struct lnk) $(&h->list));
	_ghost_stmt(struct_lnk_gather $(&h->list));
	_ghost_stmt($released(struct head) $(h));
}
