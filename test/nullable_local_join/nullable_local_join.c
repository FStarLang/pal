#include "pal.h"
#include <stdint.h>
#include <stddef.h>

struct item { uint32_t kind; uint32_t len; };

/* A test of a `_nullable` local on which both branches fall through. The
   branch that reads through the pointer leaves its pointee open, the other
   holds nothing, and the code after the test has to see one `unless_null`. */
uint32_t local_join(_nullable struct item *p)
{
    _nullable struct item *q = p;
    uint32_t r = 0;
    if (q != NULL)
    {
        r = q->len;
    }
    else
    {
        r = 1;
    }
    return r;
}

/* As above, reaching the pointee through an `&&` chain. */
uint32_t local_join_chain(_nullable struct item *p)
{
    _nullable struct item *q = p;
    uint32_t r = 0;
    if (q != NULL && q->kind == 2 && q->len > 0)
    {
        r = q->len;
    }
    return r;
}
