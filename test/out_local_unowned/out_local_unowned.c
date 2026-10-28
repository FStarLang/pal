#include "pal.h"
#include <stdint.h>

void initialize(_out int32_t *p)
{
    *p = 42;
}

void missing_storage(_plain int32_t *p)
    _requires(_inline_pulse(emp))
{
    int32_t *destination = p;
    initialize(destination);
}
