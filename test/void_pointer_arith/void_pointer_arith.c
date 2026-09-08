#include "pal.h"
#include <stdint.h>

void access_io(void *address);

void test_addressing(void *base, uint32_t slot, uint32_t slot_size)
{
    access_io(base + 4);

    void *slot_address = base + slot * slot_size;
    access_io(slot_address);
}
