#include "pal.h"

long address_taken_rank(void)
{
    long long value = 1;
    void *p = &value;
    return *(long *)p;
}
