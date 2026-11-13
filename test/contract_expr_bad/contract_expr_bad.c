#include "pal.h"

/* An untranslated contract expression is named, with its line, so the
   author can find which clause was dropped. */
int f(int x) _requires(x) _ensures(return == 0);

int f(int x) { return 0; }
