#include "pal.h"
#include <stdint.h>

void address_is_not_ownership(_plain _array uint32_t *a, uint32_t i)
{
    _plain uint32_t *p = &a[i];
    _ghost_stmt(let v = uint32_t_read $(p));
}
