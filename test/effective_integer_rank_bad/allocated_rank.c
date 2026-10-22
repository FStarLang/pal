#include "pal.h"
#include <stdlib.h>

void allocated_rank_read(void)
{
    void *p = malloc(sizeof(long));
    if (!p)
        return;
    *(long *)p = 1;
    long long value = *(long long *)p;
    free(p);
}
