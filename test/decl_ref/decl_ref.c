#include "pal.h"
#include <stdint.h>

/* --- Enum constants --- */

enum color { RED = 0, GREEN = 1, BLUE = 2 };

/* Enum constants in function body are inlined as integer literals */
int32_t use_enum_literal()
    _ensures(return == 1)
{
    return GREEN;
}

/* Enum values used in comparisons and returns */
int32_t enum_to_int(uint32_t c)
    _ensures(c == 0 ==> return == 0)
    _ensures(c == 1 ==> return == 1)
    _ensures(c == 2 ==> return == 2)
{
    if (c == RED) return 0;
    if (c == GREEN) return 1;
    return 2;
}

/* --- Const global variables (auto-detected as pure) --- */

const int32_t ANSWER = 42;

int32_t get_answer()
    _ensures(return == ANSWER)
{
    return ANSWER;
}

const int32_t OFFSET = 10;

int32_t get_offset()
    _ensures(return == OFFSET)
{
    return OFFSET;
}

/* --- Enum in expressions --- */

enum direction { NORTH = 0, SOUTH = 1, EAST = 2, WEST = 3 };

int32_t opposite(uint32_t d)
    _ensures(d == 0 ==> return == 1)
    _ensures(d == 1 ==> return == 0)
    _ensures(d == 2 ==> return == 3)
    _ensures(d == 3 ==> return == 2)
{
    if (d == NORTH) return SOUTH;
    if (d == SOUTH) return NORTH;
    if (d == EAST) return WEST;
    return EAST;
}
