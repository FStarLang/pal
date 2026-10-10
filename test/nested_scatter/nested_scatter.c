#include "pal.h"
#include <stdlib.h>

/* A struct-typed field of an object that is being filled one field at a time
   is filled the same way: the object is scattered, the field's own storage is
   scattered in turn, and each is gathered once its last field is written. */

struct lnk {
	struct lnk *next;
	struct lnk *prev;
};

struct head {
	struct lnk list;
	unsigned int qlen;
	int lock;
};

struct outer {
	int tag;
	struct head h;
};

unsigned int local_nested(void)
{
	struct head h;
	h.list.next = 0;
	h.list.prev = 0;
	h.qlen = 3;
	h.lock = 0;
	return h.qlen;
}

/* The scalar fields first, and the nested one finishing the object. */
unsigned int local_nested_last(void)
{
	struct head h;
	h.qlen = 3;
	h.lock = 0;
	h.list.prev = 0;
	h.list.next = 0;
	return h.qlen;
}

/* A nested field that is already a value can be read while the object around
   it is still being filled. */
_Bool local_nested_read_early(void)
{
	struct head h;
	h.list.next = 0;
	h.list.prev = 0;
	_Bool r = h.list.next == 0;
	h.qlen = 1;
	h.lock = 0;
	return r;
}

/* Two levels deep. */
int local_two_levels(void)
{
	struct outer o;
	o.h.list.next = 0;
	o.h.list.prev = 0;
	o.tag = 7;
	o.h.qlen = 0;
	o.h.lock = 0;
	return o.tag;
}

/* Going out of scope half-built: the nested field gives its written fields
   up and becomes storage again before the object around it does. */
int local_partial_inner(void)
{
	struct head h;
	h.list.next = 0;
	h.qlen = 1;
	return 0;
}

int local_partial_two_levels(void)
{
	struct outer o;
	o.h.list.next = 0;
	o.h.list.prev = 0;
	o.tag = 1;
	return 0;
}

/* Storage the contract hands over unwritten, through a pointer. */
void unfold_nested(_plain struct head *h)
_requires(_inline_pulse(struct_head_pts_to_uninit $(h)))
_ensures(_inline_pulse(exists* v. struct_head_pts_to $(h) 1.0R v))
{
	_ghost_stmt($unfold-uninit(struct head) $(h));
	h->list.prev = h->list.next = (struct lnk *)h;
	h->qlen = 0;
	h->lock = 0;
}

/* A freshly allocated block. */
unsigned int alloc_nested(void)
{
	struct head *h = malloc(sizeof(struct head));
	if (h == NULL)
		return 0;
	h->list.next = 0;
	h->list.prev = 0;
	h->qlen = 5;
	h->lock = 0;
	unsigned int r = h->qlen;
	free(h);
	return r;
}

/* Storage the contract hands over already in pieces, with one field holding a
   value the body leaves alone: `$scattered` says the object has been taken
   apart, so the writes fill the rest by address without scattering it again,
   and nothing is gathered because the body does not write every field. */
void fill_rest(_plain struct head *h)
_requires(_inline_pulse(
	struct_head_padding $(h) 1.0R **
	struct_lnk_pts_to_uninit ($(h) +! struct_head_offsetof_list) **
	uint32_t_pts_to_uninit ($(h) +! struct_head_offsetof_qlen) **
	(exists* (l: Int32.t). int32_t_pts_to ($(h) +! struct_head_offsetof_lock) 1.0R l)))
_ensures(_inline_pulse(exists* v. struct_head_pts_to $(h) 1.0R v))
{
	_ghost_stmt($scattered(struct head) $(h));
	h->list.next = (struct lnk *)h;
	h->list.prev = (struct lnk *)h;
	h->qlen = 0;
	_ghost_stmt(struct_head_gather $(h));
}

/* The same, but the body goes on using the object afterwards. The author's
   own gather is what makes it whole -- the emitter cannot see that, because
   the field it never writes was already a value -- so `$gathered` says so,
   and the write that follows focuses the field instead of filling it. */
void fill_rest_then_use(_plain struct head *h)
_requires(_inline_pulse(
	struct_head_padding $(h) 1.0R **
	struct_lnk_pts_to_uninit ($(h) +! struct_head_offsetof_list) **
	uint32_t_pts_to_uninit ($(h) +! struct_head_offsetof_qlen) **
	(exists* (l: Int32.t). int32_t_pts_to ($(h) +! struct_head_offsetof_lock) 1.0R l)))
_ensures(_inline_pulse(exists* v. struct_head_pts_to $(h) 1.0R v))
{
	_ghost_stmt($scattered(struct head) $(h));
	h->list.next = (struct lnk *)h;
	h->list.prev = (struct lnk *)h;
	h->qlen = 0;
	_ghost_stmt(struct_head_gather $(h));
	_ghost_stmt($gathered(struct head) $(h));
	h->qlen = h->qlen + 1;
}

/* Every field written -- each one storage until then -- and the object is a
   value again, so it is gathered. */
void fill_all(_plain struct head *h)
_requires(_inline_pulse(
	struct_head_padding $(h) 1.0R **
	struct_lnk_pts_to_uninit ($(h) +! struct_head_offsetof_list) **
	uint32_t_pts_to_uninit ($(h) +! struct_head_offsetof_qlen) **
	int32_t_pts_to_uninit ($(h) +! struct_head_offsetof_lock)))
_ensures(_inline_pulse(exists* v. struct_head_pts_to $(h) 1.0R v))
{
	_ghost_stmt($scattered(struct head) $(h));
	h->qlen = 0;
	h->lock = 0;
	h->list.next = 0;
	h->list.prev = 0;
}

/* A branch that leaves an object part-way through being filled, with the
   storage of a nested field still out of its parent, has to carry that across
   the join. The arms agree, so the code after the `if` continues the fill it
   started rather than scattering what is already scattered. */
unsigned int join_nested(int c)
{
	struct outer o;
	o.tag = 0;
	if (c) {
		o.h.list.next = 0;
	} else {
		o.h.list.next = 0;
	}
	o.h.list.prev = 0;
	o.h.qlen = 1;
	o.h.lock = 0;
	return o.h.qlen;
}
