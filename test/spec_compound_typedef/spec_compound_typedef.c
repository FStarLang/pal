#include <stdint.h>
#include "pal.h"

/* A compound literal written with a typedef name, used in an _assert: the
   check after merge must resolve the typedef to its struct. */
typedef struct _H { uintptr_t Value; } H;
#define H_NULL ((H){.Value = 0})

H get(void)
    _ensures(return.Value != 0);

void f(void)
{
    H s = H_NULL;
    s = get();
    _assert(!(s.Value == H_NULL.Value));
}
