#include "pal.h"
#include <stdint.h>

/*
 * Negative for `sizeof(<expression>)` in an annotation: the bound taken from
 * the operand's type must actually be enforced. A caller that may push onto a
 * full list cannot prove the callee's precondition.
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
	l->count += 1;
}

/* The list may already be full. */
void push_any(struct list *l)
{
	push(l);
}
