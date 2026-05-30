#include "pal.h"

void cleanup_on_error(int *p)
{
    *p = 0;
    if (*p != 0)
        goto fail;
    *p = 42;
fail:;
}

int cleanup_on_error2()
    _ensures(return == 30)
{
    int p = 0;
    if (p != 0)
        goto fail;
    p = 42;
fail: _ensures(_live(p))
    p = 30;
    return p;
}
