#include "colors.h"

_Bool
color_is_known(COLOR c)
{
    _Bool known = 0;

    switch (c)
    {
    case Color_Red:
    case Color_Green:
    case Color_Blue:
        known = 1;
        break;
    default:
        break;
    }

    return known;
}

COLOR
color_default(void)
{
    return Color_Green;
}
