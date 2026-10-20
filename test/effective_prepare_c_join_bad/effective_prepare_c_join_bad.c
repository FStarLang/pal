#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

void join_different_types(int flag)
{
    void *p = malloc(16);
    if (!p)
        return;
    if (flag)
        _ghost_stmt($prepare(int) $(p));
    else
        _ghost_stmt($prepare(float) $(p));
    free(p);
}
