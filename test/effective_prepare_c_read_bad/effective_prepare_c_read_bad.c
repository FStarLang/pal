#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

int read_uninitialized_allocation(void)
{
    void *p = malloc(16);
    if (!p)
        return 0;
    int result = *(int *)p;
    free(p);
    return result;
}
