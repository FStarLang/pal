#include "pal.h"
#include <stdint.h>

typedef union cell { uint8_t tag; uint64_t bits; } cell;
struct entry { uint32_t count; cell saved; };
union _overlay view { struct entry entry; uint64_t prefix; };

/* Initializing the first member doesn't initialize the rest as uint64_t. */
cell clear(struct entry *p)
    _ensures(_inline_pulse(pure (Union_cell.union_cell_repr
        (Union_cell.Union_cell_bits 0UL) $(p->saved))))
{
    *p = (struct entry){0};
    return p->saved;
}
