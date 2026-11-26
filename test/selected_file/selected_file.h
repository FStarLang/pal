#pragma once
#include "pal.h"
#include <stdint.h>

int32_t kept(int32_t input)
    _requires(input < 100)
    _ensures(return == input + 1);

static int32_t header_value(void)
    _ensures(return == 7)
{
    return 7;
}
