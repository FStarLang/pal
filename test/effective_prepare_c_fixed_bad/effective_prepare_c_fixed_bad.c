#include "pal.h"
#include <stdint.h>

void prepare_declared(void)
{
    int declared = 7;
    _ghost_stmt($prepare(float) $(&declared));
}
