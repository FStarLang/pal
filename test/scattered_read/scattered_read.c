#include "pal.h"
#include <stdint.h>

/* An object a contract hands over in pieces behind a predicate, some fields
   with values and one never written. `$scattered` says the object is in
   pieces, so a read of a field the body has not written goes by address to
   that field's own points-to, instead of focusing the whole object, which
   would need every field to hold a value. A struct-typed field named by its
   own `$scattered` is in pieces inside it, and reads through it go by address
   too. This is the shape of a handler reading a wrapper its submitter
   never finished. `scattered_read_no_cell` and `scattered_read_uninit` are
   the controls: the read still needs the field's points-to with a value. */

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
