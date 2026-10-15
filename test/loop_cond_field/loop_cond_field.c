// A loop condition that reads a field through a pointer (#359).
#include "pal.h"

struct dev {
	int n;
};

_requires(d->n >= 0)
void walk(struct dev *d)
{
	int i;

	for (i = 0; i < d->n; i++)
		_invariant(_live(*d))
		_invariant(i >= 0 && i <= d->n)
	{
	}
}

// The body shrinks the bound, so the condition must re-read it each time.
_requires(d->n >= 0)
_ensures(d->n >= 0)
void shrink(struct dev *d)
{
	int i;

	for (i = 0; i < d->n; i++)
		_invariant(_live(*d))
		_invariant(i >= 0 && d->n >= 0)
	{
		d->n = d->n - 1;
	}
}

struct ring {
	unsigned int count;
	unsigned int data[8];
};

_requires(r->count <= 8)
_ensures(return <= 8)
unsigned int sum_until(struct ring *r)
{
	unsigned int i = 0;

	while (i < r->count && r->data[i] != 0)
		_invariant(_live(*r))
		_invariant(r->count <= 8 && i <= r->count)
	{
		i++;
	}
	return i;
}
