#include "pal.h"

int foo()
{
	int x = 1;
	int *y = &x;
	return x;
}

int foo2()
{
	int x = 1;
	int *y = &x;
	*y = 2;
	return x;
}
