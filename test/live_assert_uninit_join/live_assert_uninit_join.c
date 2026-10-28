#include "pal.h"

void uninitialized_join(void)
{
    int x;
    goto done;
done:
    _ensures(_live(x))
    return;
}
