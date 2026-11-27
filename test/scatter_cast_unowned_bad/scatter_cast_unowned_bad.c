#include "pal.h"

/* A `$scattered` hint on a cast local names storage; it does not give it.
   With no ownership of the object, the write through the local is refused. */

struct head {
	unsigned int qlen;
	int lock;
};

void write_unowned(_plain void *e)
_requires(_inline_pulse(emp))
_ensures(_inline_pulse(emp))
{
	struct head *h = (struct head *)e;
	_ghost_stmt($scattered(struct head) $(h));
	h->qlen = 1;
	_ghost_stmt($released(struct head) $(h));
}
