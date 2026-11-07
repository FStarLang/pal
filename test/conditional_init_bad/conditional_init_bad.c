#include "pal.h"
#include <stdint.h>

void initialized_on_one_path(int *p, _Bool write)
{
    int x;
    if (write)
        _ensures(*p == 1)
    {
        x = 1;
        *p = x;
    }
    _assert(_live(x));
}
