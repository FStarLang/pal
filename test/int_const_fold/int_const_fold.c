#include "pal.h"
#include <limits.h>
#include <stddef.h>
#include <stdint.h>

/* Integer constant expressions in code are folded to one literal of their
   type: musl's word masks below are `72340172838076673sz` and
   `9259542123273814144sz`, not trees of `int` operations each carrying an
   overflow obligation. One with undefined behaviour is not folded. */

#define ONES ((size_t)-1 / UCHAR_MAX)
#define HIGHS (ONES * (UCHAR_MAX / 2 + 1))

size_t ones(void)
	_ensures(return == 72340172838076673)
{
	return ONES;
}

size_t highs(void)
	_ensures(return == 9259542123273814144)
{
	return HIGHS;
}

int half(void)
	_ensures(return == 128)
{
	return UCHAR_MAX / 2 + 1;
}

uint8_t narrow(void)
	_ensures(return == 44)
{
	return (uint8_t)300;
}

unsigned wrap(void)
	_ensures(return == 4294967295)
{
	return 0u - 1;
}
