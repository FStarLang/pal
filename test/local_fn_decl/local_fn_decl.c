#include "pal.h"

/* C allows declaring a function in block scope: the K&R-era idiom of
   declaring a library function locally instead of including its header.
   The declaration is hoisted to file scope, so the call resolves. */

double local_decl(_array double *v, unsigned n)
  _preserves(v._length == n)
  _requires(n > 0)
{
    double pal_floor();
    double d = pal_floor();
    return v[0] + d;
}

/* Declared locally in one function, called from another. */

unsigned other_caller(void)
{
    unsigned pal_get(void);
    return pal_get();
}

unsigned redeclarer(void)
{
    unsigned pal_get(void);
    return pal_get();
}
