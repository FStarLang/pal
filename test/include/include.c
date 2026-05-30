#include "pal.h"
#include "constants.h"

int get_magic(void)
    _ensures(return == 42)
{
    return MAGIC_VALUE;
}
