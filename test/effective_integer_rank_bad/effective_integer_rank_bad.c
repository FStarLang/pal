#include "pal.h"
#include <stdint.h>
long direct_rank_read(long long *p)
{
    return *(long *)p;
}
