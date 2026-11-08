#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

/* After the join, the storage holds an `int` or a `float`; reading it as an
   `int` is undefined on the second path. */
int join_different_types(int flag)
{
    void *p = malloc(16);
    if (!p)
        return 0;
    if (flag)
        *(int *)p = 1;
    else
        *(float *)p = 1.25f;
    int result = *(int *)p;
    free(p);
    return result;
}
