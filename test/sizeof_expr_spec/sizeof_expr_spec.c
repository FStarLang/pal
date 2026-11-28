#include "pal.h"
#include <stdint.h>

/*
 * `sizeof(<expression>)` inside an annotation. C code commonly guards an
 * append into a fixed-size array with a fatal check written through an
 * array-size macro, and such a check is lowered to `_assert`. The annotation
 * language used to take only `sizeof(<type>)`, so the macro could not appear
 * in a specification at all ("unknown function sizeof"). The operand is now
 * typed and the expression stands for `sizeof` of that type; the operand is
 * never evaluated, as in C.
 */

#define ARRAY_SIZE(x) (sizeof(x) / sizeof(*(x)))

/* `count` slots of `items` are in use; a push claims the next one. */
struct list {
	uint32_t count;
	uint64_t items[5];
};

void push(struct list *l)
	_requires(l->count < ARRAY_SIZE(l->items))
	_ensures(l->count == _old(l->count) + 1)
{
	_assert(l->count < ARRAY_SIZE(l->items));
	_assert(sizeof(l->count) == sizeof(uint32_t));
	_assert(sizeof(l->items[0]) == sizeof(uint64_t));
	_assert(sizeof(l->items) == sizeof(uint64_t[5]));
	l->count += 1;
}

/* The bound is the array's own, five, not a constant spelled differently. */
void push_two(struct list *l)
	_requires(l->count < 3)
{
	push(l);
	push(l);
}
