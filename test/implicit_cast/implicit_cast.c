#include "pal.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* Test: pointer as if-condition (CK_PointerToBoolean).
   Uses _plain since the pointer may be null. */
int32_t write_if_nonnull(_plain int32_t *p)
{
    if (p) {
        return 1;
    }
    return 0;
}

/* Test: negated pointer as condition */
int32_t return_if_null(_plain int32_t *p)
{
    if (!p) {
        return 0;
    }
    return 1;
}

/* Test: pointer to bool conversion in return */
bool is_nonnull(_plain int32_t *p)
    _ensures(return == (p != 0))
{
    return p;
}

/* Test: pointer as ternary condition (CK_PointerToBoolean) */
int32_t select_by_ptr(_plain int32_t *p, int32_t fallback)
    _ensures(p == 0 ==> return == fallback)
{
    return p ? 1 : fallback;
}
