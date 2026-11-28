#include "pal.h"
#include <stddef.h>

/* A pointer local declared NULL and then set once from a call names the same
   storage at every use, as one declared with the call does, when a
   `$scattered` hint further on names it, here in one arm only: a read of a
   field goes by address to that field's own points-to instead of focusing the
   whole object, which this function does not hold. */

struct obj {
	void *pool;
	int count;
};

struct obj *from_ctx(_plain void *ctx)
_ensures(return == (struct obj *)ctx);

void *read_pool(_plain void *ctx, int want)
_requires(_inline_pulse(Obj_field.field $(ctx)))
_ensures(_inline_pulse(Obj_field.field $(ctx)))
{
	struct obj *o = NULL;
	void *r;
	o = from_ctx(ctx);
	_ghost_stmt(rewrite each $(ctx) as $(o));
	if (want) {
		_ghost_stmt(unfold Obj_field.field $(o));
		_ghost_stmt($scattered(struct obj) $(o));
		r = o->pool;
		_ghost_stmt($gathered(struct obj) $(o));
		_ghost_stmt(fold Obj_field.field $(o));
	} else {
		r = NULL;
	}
	_ghost_stmt(rewrite each $(o) as $(ctx));
	return r;
}
