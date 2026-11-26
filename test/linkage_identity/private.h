#pragma once
#include "pal.h"
#include <stdint.h>

static const int32_t header_number = UNIT_VALUE;
static int32_t header_cell;
static int32_t header_value(void)
    _ensures(_inline_pulse(pure ($(return) == $(header_number))))
    _ensures(return == UNIT_VALUE)
{
    return header_number;
}
static _plain int32_t *header_address(void)
    _ensures(return == &header_cell)
{
    return &header_cell;
}

static _block_storage _plain int32_t *site_address(int32_t first)
{
#define RETURN_SITE() do { static int32_t cell = UNIT_VALUE; return &cell; } while (0)
    if (first) { RETURN_SITE(); } else { RETURN_SITE(); }
#undef RETURN_SITE
}
