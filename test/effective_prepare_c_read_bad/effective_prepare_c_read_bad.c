#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

int read_prepared(void)
{
    void *p = malloc(16);
    if (!p)
        return 0;
    _ghost_stmt($prepare(int) $(p));
    int result = *(int *)p;
    free(p);
    return result;
}
