#include "pal.h"
#include <stdint.h>

/* Two function pointers stored in local structs, each struct's address handed
 * to a callee. Each hand-off makes the seeded validity "laundered", and at the
 * end of the body both are put down. With more than one in context, putting
 * them down by inference (`drop_is_valid _ _ _`) cannot pick between them. */

int32_t add(int32_t a, int32_t b)
    _requires(a > 0 && a < 100 && b > 0 && b < 100)
    _ensures(return == a + b)
{
    return a + b;
}

int32_t neg(int32_t a)
    _requires(a > -100 && a < 100)
    _ensures(return == -a)
{
    return -a;
}

struct ops2 {
    int32_t (*bin)(int32_t, int32_t);
    int32_t (*un)(int32_t);
};

void take(_plain struct ops2 const* o);

void two_tables(void)
{
    struct ops2 const a = { .bin = add };
    take(&a);
    struct ops2 const b = { .un = neg };
    take(&b);
}
