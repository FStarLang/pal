#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

uint32_t StageView(uint32_t state)
    _ensures(return == state)
{
    return state;
}

uint32_t select_state_from_flag(bool IsWrite)
    _ensures(return == 1u || return == 2u)
{
    return StageView(IsWrite ? 2u : 1u);
}

uint32_t select_state_from_locals(bool IsWrite)
    _ensures(return == 1u || return == 2u)
{
    uint32_t StateRead = 1u;
    uint32_t StateWrite = 2u;
    return StageView(IsWrite ? StateWrite : StateRead);
}
