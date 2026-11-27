#include "pal.h"
#include <stdint.h>

/* Control for `scattered_read`: the contract's pieces do not include the
   field read. The read goes by address, and so needs that field's own
   points-to, which nothing holds. */

struct params {
	void *filter;
	void *cursor;
	uint32_t start;
};

struct wrapper {
	void *request;
	struct params inner;
	int32_t status;
};


void *read_written(_plain struct wrapper *w)
_requires(_inline_pulse(Wrapper_pieces.pieces $(w)))
_ensures(_inline_pulse(Wrapper_pieces.pieces $(w)))
{
	void *r;
	_ghost_stmt(Wrapper_pieces.open_pieces $(w));
	_ghost_stmt($scattered(struct wrapper) $(w));
	_ghost_stmt($scattered(struct params) $(&w->inner));
	if (w->status != 0)
		r = w->request;
	else
		r = w->inner.cursor;
	_ghost_stmt(Wrapper_pieces.close_pieces $(w));
	return r;
}
