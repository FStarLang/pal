#include "pal.h"
#include <stddef.h>
#include <stdint.h>

void rebind_optional(_nullable _out int32_t *p)
    _requires(p != NULL)
{
    _ghost_stmt(elim_unless_null $(p) (int32_t_pts_to_uninit $(p)));
    int32_t local;
    p = &local;
    *p = 42;
}
