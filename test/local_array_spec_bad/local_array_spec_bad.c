#include "pal.h"
#include <stddef.h>

/* An invariant reading a cell of a local array claims the cell has been
   written: `bs[1]` is never stored, so this must not verify. */
size_t unwritten(size_t n)
{
	size_t bs[2];
	size_t i;
	bs[0] = 0;
	for (i = 0; i < n; i++)
		_invariant(bs[0] == 0 && bs[1] == bs[1])
	{
	}
	return bs[0];
}
