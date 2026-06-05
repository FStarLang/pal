#include "pal.h"
#include <stdint.h>

_arrayptr int* via_addressof_const(_array int* a)
{
    return &a[3];
}

typedef struct containercopy {
    _array int* Elements;
} containercopy;

_arrayptr int* get_via_addressof_const(containercopy* c)
{
    return &c->Elements[3];
}
