#include "pal.h"
#include <stddef.h>
#include <stdint.h>

void write_required(_out int32_t *p)
{
    *p = 42;
}

void call_required_with_null(void)
{
    write_required(NULL);
}
