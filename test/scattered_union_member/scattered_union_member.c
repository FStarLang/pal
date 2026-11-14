// An `_out` struct filled one field at a time, where one field is a union
// written through its members: first one member, then another. The union is
// a field of the partly built struct, so writing its member must only open
// that field, and mark it written.

#include "pal.h"
#include <stdint.h>

typedef struct { uint8_t f0 : 1; uint8_t f1 : 1; } FF;
typedef union { FF F; uint8_t All; } FLAGS;

struct params { uint32_t a; FLAGS flags; _Bool b; };

void params_init(_out struct params *p, uint32_t a, _Bool b)
{
    p->a = a;
    p->flags.All = 0;
    p->b = b;
}

void params_init2(_out struct params *p, uint32_t a, FF ff, _Bool b)
{
    p->a = a;
    p->flags.All = 0;
    p->flags.F = ff;
    p->b = b;
}
