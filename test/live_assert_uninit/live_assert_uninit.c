#include "pal.h"

void uninitialized(void)
{
    int x;
    _assert(_live(x));
}
