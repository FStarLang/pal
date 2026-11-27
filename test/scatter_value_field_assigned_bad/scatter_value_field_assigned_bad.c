#include "pal.h"

/* The parameter's field is pointed elsewhere after its `$scattered` hint. The
   write that follows goes to the new object, so it must not be taken as a
   write of the object the hint named. */

struct head {
	unsigned int qlen;
	int lock;
};

struct msg {
	struct head *h;
	int tag;
};

void retarget_field(struct msg m, _plain struct head *other)
_requires(_inline_pulse(struct_head_pts_to_uninit $(m.h)))
_ensures(_inline_pulse(exists* v. struct_head_pts_to $(m.h) 1.0R v))
{
	_ghost_stmt(struct_head_scatter_uninit $(m.h));
	_ghost_stmt($scattered(struct head) $(m.h));
	m.h = other;
	m.h->qlen = 1;
	m.h->lock = 2;
	_ghost_stmt($released(struct head) $(m.h));
}
