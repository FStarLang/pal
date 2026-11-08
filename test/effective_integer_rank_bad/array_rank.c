#include "pal.h"

long array_rank_read(void)
{
    long long values[2] = { 1, 2 };
    return *(long *)values;
}
