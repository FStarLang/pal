#include "pal.h"

/* A contract clause that cannot be translated is reported at the offending
   expression in the prototype, not at the definition. */
int g(int x);
int f(int x)
	_requires(x < 10)
	_requires(1 <= g(x) + 1)
	_ensures(return == 0);

int f(int x) { return 0; }
