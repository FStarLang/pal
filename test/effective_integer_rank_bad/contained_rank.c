#include "pal.h"

struct rank_container { long long value; };

long contained_rank_read(struct rank_container *p)
{
    return *(long *)p;
}
