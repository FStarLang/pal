#include "pal.h"
#include <stdint.h>

// C11 anonymous (unnamed) aggregate members. Each must get a distinct F* field
// name; previously every unnamed member collapsed onto the same empty name,
// producing duplicate F* record fields and accessors.
struct outer {
    struct {
        int a;
    };
    struct {
        int b;
    };
};

int read_a(struct outer *o)
{
    return o->a;
}

int read_b(struct outer *o)
{
    return o->b;
}

void copy_a_to_b(struct outer *o)
{
    o->b = o->a;
}
