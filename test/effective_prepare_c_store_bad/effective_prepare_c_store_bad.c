#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

void store_wrong_type(void)
{
    void *p = malloc(16);
    if (!p)
        return;
    _ghost_stmt($prepare(int) $(p));
    *(float *)p = 1.25f;
    free(p);
}

void unsupported_pointer_target(void)
{
    void *p = malloc(16);
    if (!p)
        return;
    _ghost_stmt($prepare(int *) $(p));
    *(float **)p = NULL;
    free(p);
}
