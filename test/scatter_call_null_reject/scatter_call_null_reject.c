#include "pal.h"
#include <stddef.h>

/* As `scatter_call_null`, but the local is retargeted through its address
   after the hint. The read goes through the new pointer, not into the
   storage the hint named, and this function holds nothing of that object. */

struct obj {
	void *pool;
	int count;
};

struct obj *from_ctx(_plain void *ctx)
_ensures(return == (struct obj *)ctx);

void *read_pool(_plain void *ctx, _plain struct obj *other)
_requires(_inline_pulse(Obj_field.field $(ctx)))
_ensures(_inline_pulse(Obj_field.field $(ctx)))
{
	struct obj *o = NULL;
	void *r;
	o = from_ctx(ctx);
	_ghost_stmt(rewrite each $(ctx) as $(o));
	_ghost_stmt(unfold Obj_field.field $(o));
	_ghost_stmt($scattered(struct obj) $(o));
	struct obj **op = &o;
	*op = other;
	r = o->pool;
	_ghost_stmt($gathered(struct obj) $(o));
	_ghost_stmt(fold Obj_field.field $(o));
	_ghost_stmt(rewrite each $(o) as $(ctx));
	return r;
}
