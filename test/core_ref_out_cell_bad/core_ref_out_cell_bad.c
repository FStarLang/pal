// The cast on an `_out` argument's address is looked through only when the
// storage it claims is the slot's own Palow type (test/core_ref_out_cell).
// Anything else is a reinterpretation of the local's storage, which Palow does
// not model, and stays refused.

#include "pal.h"
#include <stdint.h>

void fill_u32(_out uint32_t* p);
void fill_ptr(_out char** p);

/* Same size, different Palow type. */
uint32_t signedness(void)
{
    int32_t x;

    fill_u32((uint32_t*)&x);
    return 0;
}

/* A pointer slot claimed over an integer. */
uint32_t int_as_pointer(void)
{
    int x;

    fill_ptr((char**)&x);
    return 0;
}

/* The address of a local array is not its first element's slot. */
uint32_t array_address(void)
{
    uint32_t a[2];

    fill_u32((uint32_t*)&a);
    return 0;
}
