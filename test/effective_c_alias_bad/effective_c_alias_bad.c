#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

float read_incompatible(void)
{
    void *p = malloc(16);
    if (!p)
        return 0.0f;
    _ghost_stmt($prepare(int) $(p));
    *(int *)p = 7;
    float result = *(float *)p;
    free(p);
    return result;
}
