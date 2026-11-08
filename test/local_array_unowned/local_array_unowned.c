#include "pal.h"
#include <stdint.h>

void unowned_local(_plain _array uint32_t *a)
    _requires(a != 0)
{
    _array uint32_t *p = 0;
    p = a;
    p[0] = 42;
}
